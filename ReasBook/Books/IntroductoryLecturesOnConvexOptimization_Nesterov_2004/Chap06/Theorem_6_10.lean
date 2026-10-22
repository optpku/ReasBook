/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_43
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_9

-- Declarations for this item will be appended below by the statement pipeline.

open RealSymmetricMatrixSpace
open scoped BigOperators
open scoped Gradient
open scoped MatrixOrder
open scoped RealSymmetricMatrixSpace

noncomputable section

universe u

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Theorem 6.10: use the ambient `L²` operator norm explicitly in the radius-ball
arguments, so those estimates do not depend on whichever auxiliary matrix norm is active
elsewhere in the file. -/
private def ambientOpNorm (A : Mat) : ℝ :=
  @norm Mat Matrix.instL2OpNormedRing.toNorm A

/-- Helper for Theorem 6.10: use the Frobenius normed-group structure on ambient matrices when
restricting the trace-power calculus back to `SymmMat`. -/
local instance theoremSixTenAmbientMatrixNormedAddCommGroup : NormedAddCommGroup Mat :=
  Matrix.frobeniusNormedAddCommGroup

/-- Helper for Theorem 6.10: scalar multiplication on ambient matrices is measured with the
Frobenius norm during the local ambient `ContDiff` argument. -/
local instance theoremSixTenAmbientMatrixNormedSpace : NormedSpace ℝ Mat :=
  Matrix.frobeniusNormedSpace

/-- Helper for Theorem 6.10: the ambient matrix ring carries the Frobenius-compatible normed-ring
structure needed by `fun_prop` on matrix powers. -/
local instance theoremSixTenAmbientMatrixNormedRing : NormedRing Mat :=
  Matrix.frobeniusNormedRing

/-- Helper for Theorem 6.10: the ambient matrix algebra over `ℝ` carries the Frobenius normed
algebra structure used by the local trace-power regularity proof. -/
local instance theoremSixTenAmbientMatrixNormedAlgebra : NormedAlgebra ℝ Mat :=
  Matrix.frobeniusNormedAlgebra

attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedSpace
attribute [local instance 1001] RealSymmetricMatrixSpace.symmetricMatrixInnerProductSpace
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace

/- Theorem 6.10 lies in the chapter's real-symmetric spectral-power-series / Hessian domain.

Sampled owner-style declarations:
- Chapter 6 `AnalyticSymmetricSpectralFunction` in `Definition_6_43`, an internal bridge owner for
  the local proof route;
- Chapter 5 `RealSymmetricMatrixSpace.eigenvalues`, the chapter owner for the ordered eigenvalue
  vector of a real symmetric matrix on `𝕊^n`;
- mathlib `CFC.abs`, together with `CFC.abs_nonneg` and Hermitian eigenvalues, as the canonical
  absolute-value owner for real symmetric matrices;
- mathlib `iteratedFDeriv` and `iteratedDeriv`, the canonical Hessian quadratic-form owner and
  one-variable second-derivative owner for scalar-valued maps;
- `powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing` in `Theorem_6_9`, the chapter
  trace-power Hessian estimate used termwise in the power-series proof route.

Best owner abstraction:
- source-facing: the Hessian quadratic-form inequality for the spectral sum
  `X ↦ ∑ i, f (λᵢ(X))` attached to a real power series with positive radius of convergence;
- core/canonical: `AnalyticSymmetricSpectralFunction`, `𝕊^n`, `eigenvalues`, `CFC.abs`,
  `iteratedFDeriv`, and `iteratedDeriv`;
- bridge/view: the power-series expansion into trace-power owners together with Theorem 6.9's
  termwise spectral bound.

Primitive data:
- a coefficient sequence `a : ℕ → ℝ` with strictly positive convergence radius;
- a symmetric matrix `X : SymmMat` and a symmetric direction `H : SymmMat`;
- the spectral-domain hypothesis that every eigenvalue of `X` lies in the scalar convergence
  ball of the power-series radius.

Derived API:
- the source-facing scalar function `theoremSixTenScalarFun a`;
- the source-facing spectral sum `theoremSixTenMatrixFun a`;
- the right-hand eigenvalue-square bound through the eigenvalues of `CFC.abs X` and
  `CFC.abs H`.

Source/core/bridge triage:
- source-facing: Theorem 6.10's Hessian bound for the spectral sum itself;
- core/canonical: the chapter `𝕊^n`, `eigenvalues`, and absolute-value owners together with
  `iteratedFDeriv`;
- bridge/view: the trace-power series decomposition used only in the proof strategy.

The public labeled theorem stays source-facing on the coefficient sequence `a : ℕ → ℝ` and its
induced scalar and matrix functions. The chapter owner `AnalyticSymmetricSpectralFunction`
remains only an internal proof bridge and is not part of the source-facing theorem surface.
-/

namespace AnalyticSymmetricSpectralFunction

/- The target proof uses two reusable bridges: first, Theorem 6.9 remains valid after scaling
each trace-power term by the nonnegative coefficient `Φ.coeff k`; second, the scalar slice
`t ↦ Φ.matrixFun (X + t • H)` has second derivative equal to the ambient Hessian quadratic form
whenever `Φ.matrixFun` is `C²` at `X`. -/

/-- Helper for Theorem 6.10: a `C²` scalar-valued map on `SymmMat` has a differentiable gradient,
so Chapter 5's Hessian quadratic-form identity applies. -/
lemma differentiableAt_gradient_of_contDiffAt_two
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {x : E} (hcont : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  -- Rewrite the gradient through the Riesz map so differentiability reduces to `fderiv`.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    exact
      (hcont.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Theorem 6.10: on any real normed space, the affine line `t ↦ x + t • d` has
derivative `d`. -/
lemma affineLineHasDerivAt_generic
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul, add_comm] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 6.10: on any real normed space, an affine line has vanishing second
iterated derivative. -/
lemma affineLineIteratedDerivTwo_generic
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x d : E) :
    iteratedDeriv 2 (fun s : ℝ ↦ x + s • d) = fun _ : ℝ ↦ (0 : E) := by
  -- Differentiate the affine line once to a constant, then differentiate that constant again.
  funext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ ↦ x + s • d) = fun _ : ℝ ↦ d := by
    funext s
    exact (affineLineHasDerivAt_generic x d s).deriv
  rw [hderiv, deriv_const]

/-- Helper for Theorem 6.10: a `C²` scalar-valued map has its repeated second Fréchet derivative
on a repeated direction equal to the Chapter 5 second directional derivative. -/
lemma iteratedFDerivTwo_apply_eqSecondDirectionalDerivative_of_contDiffAtTwo
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x h : E} (hcont : ContDiffAt ℝ 2 f x) :
    iteratedFDeriv ℝ 2 f x ![h, h] = secondDirectionalDerivative f x h := by
  let line : ℝ → E := fun t ↦ x + t • h
  have hline₂ : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  have hcomp :
      iteratedDeriv 2 (f ∘ line) 0 =
        (iteratedFDeriv ℝ 2 f (line 0)) (fun _ ↦ deriv line 0) +
          (fderiv ℝ f (line 0)) (iteratedDeriv 2 line 0) := by
    simpa [line] using (iteratedDeriv_vcomp_two (by simpa [line] using hcont) hline₂)
  have hline_deriv : deriv line 0 = h := by
    simpa [line] using (affineLineHasDerivAt_generic x h 0).deriv
  rw [secondDirectionalDerivative]
  symm
  calc
    iteratedDeriv 2 (directionalSlice f x h) 0 = iteratedDeriv 2 (f ∘ line) 0 := by
      rfl
    _ =
        (iteratedFDeriv ℝ 2 f (line 0)) (fun _ ↦ deriv line 0) +
          (fderiv ℝ f (line 0)) (iteratedDeriv 2 line 0) := hcomp
    _ = iteratedFDeriv ℝ 2 f x ![h, h] := by
      rw [affineLineIteratedDerivTwo_generic]
      simp [line, hline_deriv, iteratedFDeriv_two_apply]

/-- Helper for Theorem 6.10: the affine slice `t ↦ X + t • H` has constant derivative `H`. -/
lemma affineLineHasDerivAt
    (X H : SymmMat) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ X + s • H) H t := by
  -- Route correction: keep the affine derivative on the exact slice spelling used later instead
  -- of asking simplification to recover the left-translation by `X`.
  simpa [one_smul, add_comm] using ((hasDerivAt_id t).smul_const H).const_add X

/-- Helper for Theorem 6.10: the affine slice `t ↦ X + t • H` has vanishing second derivative. -/
lemma affineLineIteratedDerivTwo
    (X H : SymmMat) :
    iteratedDeriv 2 (fun s : ℝ ↦ X + s • H) = fun _ : ℝ ↦ (0 : SymmMat) := by
  -- Route correction: the second derivative also reduces to the generic affine-line computation
  -- once the local `SymmMat` calculus owner is canonical.
  simpa using affineLineIteratedDerivTwo_generic X H

/-- Helper for Theorem 6.10: for `C²` scalar-valued maps on `SymmMat`, the repeated second
Fréchet derivative in a repeated direction agrees with Chapter 5's second directional derivative. -/
lemma iteratedFDeriv_two_apply_eq_secondDirectionalDerivative
    {f : SymmMat → ℝ} {X H : SymmMat} (hcont : ContDiffAt ℝ 2 f X) :
    iteratedFDeriv ℝ 2 f X ![H, H] = secondDirectionalDerivative f X H := by
  -- Route correction: the generic Hilbert-space bridge is already stated on the canonical local
  -- `SymmMat` owner stack, so this step is only a direct specialization.
  simpa using
    iteratedFDerivTwo_apply_eqSecondDirectionalDerivative_of_contDiffAtTwo hcont

/-- Helper for Theorem 6.10: for any `C²` scalar-valued map on `SymmMat`, the affine slice
`t ↦ f (X + t • H)` has second derivative at `0` equal to the ambient Hessian quadratic form in
the direction `H`. -/
lemma slice_secondDeriv_eq_iteratedFDeriv_two
    {f : SymmMat → ℝ} {X H : SymmMat} (hcont : ContDiffAt ℝ 2 f X) :
    iteratedDeriv 2 (fun t : ℝ ↦ f (X + t • H)) 0 =
      (iteratedFDeriv ℝ 2 f X) ![H, H] := by
  -- Unfold the scalar slice to the Chapter 5 directional derivative owner, then rewrite it back
  -- through the repeated-direction Hessian bridge.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ f (X + t • H)) 0 = secondDirectionalDerivative f X H := by
      rw [secondDirectionalDerivative]
      rfl
    _ = (iteratedFDeriv ℝ 2 f X) ![H, H] := by
      exact (iteratedFDeriv_two_apply_eq_secondDirectionalDerivative hcont).symm

/-- Helper for Theorem 6.10: tracing the ambient matrix representative is additive on the exact
local `SymmMat` carrier. -/
private theorem traceSymm_map_add (X Y : SymmMat) :
    Matrix.trace (((X + Y : SymmMat) : Mat)) =
      Matrix.trace (X : Mat) + Matrix.trace (Y : Mat) := by
  -- Reduce the symmetric-matrix addition to ambient matrix addition before applying trace
  -- linearity.
  simp [Matrix.trace_add]

/-- Helper for Theorem 6.10: tracing the ambient matrix representative is homogeneous on the
exact local `SymmMat` carrier. -/
private theorem traceSymm_map_smul (c : ℝ) (X : SymmMat) :
    Matrix.trace (((c • X : SymmMat) : Mat)) = c * Matrix.trace (X : Mat) := by
  -- Scalar multiplication on `SymmMat` is inherited from the ambient matrix space.
  simp [Matrix.trace_smul]

/-- Helper for Theorem 6.10: the ambient trace defines a linear functional on the exact local
`SymmMat` carrier used by this file. -/
private abbrev ambientTraceLinearMap : Mat →ₗ[ℝ] ℝ :=
  @Matrix.traceLinearMap (Fin n) ℝ ℝ inferInstance inferInstance inferInstance inferInstance

/-- Helper for Theorem 6.10: the ambient trace defines a linear functional on the exact local
`SymmMat` carrier used by this file. -/
private def traceSymmLinearMap : SymmMat →ₗ[ℝ] ℝ :=
  ambientTraceLinearMap.comp (Submodule.subtype (𝕊^n : Submodule ℝ Mat))

/-- Helper for Theorem 6.10: finite dimensionality makes the symmetric-matrix trace functional
continuous. -/
private theorem traceSymmLinearMap_continuous :
    Continuous (traceSymmLinearMap : SymmMat → ℝ) := by
  -- The exact local `SymmMat` carrier is finite dimensional, so every linear map is continuous.
  exact traceSymmLinearMap.continuous_of_finiteDimensional

/-- Helper for Theorem 6.10: package the exact local symmetric-matrix trace as a continuous linear
map so the affine `k = 1` branch can be proved without crossing the imported owner boundary. -/
private def traceSymmContinuousLinearMap : SymmMat →L[ℝ] ℝ :=
  ⟨traceSymmLinearMap, traceSymmLinearMap_continuous⟩

/-- Helper for Theorem 6.10: evaluating the packaged symmetric-matrix trace recovers the ambient
matrix trace. -/
@[simp] private theorem traceSymmContinuousLinearMap_apply (X : SymmMat) :
    traceSymmContinuousLinearMap X = Matrix.trace (X : Mat) :=
  by
    simp [traceSymmContinuousLinearMap, traceSymmLinearMap, ambientTraceLinearMap]

/-- Helper for Theorem 6.10: any continuous linear functional on `SymmMat` sends the affine line
`t ↦ X + t • H` to the scalar affine function `t ↦ L X + t * L H`. -/
private lemma continuousLinearMap_apply_affineLine
    (L : SymmMat →L[ℝ] ℝ) (X H : SymmMat) :
    (fun t : ℝ ↦ L (X + t • H)) = fun t : ℝ ↦ L X + t * L H := by
  -- Expand the linearity of `L` along the affine line and rewrite scalar multiplication in the
  -- scalar codomain as ordinary multiplication.
  funext t
  simp [map_add, map_smul, smul_eq_mul]

/-- Helper for Theorem 6.10: package ambient matrix trace as a continuous linear map with a
Theorem 6.10-local name, so later ambient restriction steps can avoid imported private owners. -/
private def theoremSixTenTraceContinuousLinearMap : Mat →L[ℝ] ℝ :=
  ⟨ambientTraceLinearMap, ambientTraceLinearMap.continuous_of_finiteDimensional⟩

/-- Helper for Theorem 6.10: evaluating the local packaged ambient trace map recovers the usual
trace. -/
@[simp] private theorem theoremSixTenTraceContinuousLinearMap_apply (A : Mat) :
    theoremSixTenTraceContinuousLinearMap A = Matrix.trace A :=
  by
    simp [theoremSixTenTraceContinuousLinearMap, ambientTraceLinearMap]

/-- Helper for Theorem 6.10: package the operator norm of the local ambient trace map with the
matrix size explicit in the type, so later estimates do not have to infer it repeatedly. -/
private def theoremSixTenTraceContinuousLinearMapNorm : ℝ :=
  ‖(theoremSixTenTraceContinuousLinearMap : Mat →L[ℝ] ℝ)‖

/-- Helper for Theorem 6.10: package the symmetric-subtype inclusion as a continuous linear map
with a local name, so later chain-rule steps can stay on one explicit owner. -/
private def theoremSixTenSymmetricInclusion : SymmMat →L[ℝ] Mat :=
  (Submodule.subtypeₗᵢ (𝕊^n)).toContinuousLinearMap

/-- Helper for Theorem 6.10: evaluating the local bundled inclusion recovers the ambient matrix
representative of a symmetric matrix. -/
@[simp] private theorem theoremSixTenSymmetricInclusion_apply (X : SymmMat) :
    theoremSixTenSymmetricInclusion X = (X : Mat) :=
  by
    simp [theoremSixTenSymmetricInclusion]

/-- Helper for Theorem 6.10: the source-facing trace-power owner is exactly the ambient matrix
trace of the ambient representative raised to the same power. -/
private theorem powerTrace_eq_ambientTracePow
    (k : ℕ) (X : SymmMat) :
    π[k] X = Matrix.trace (((X : Mat)) ^ k) := by
  -- Unfold the chapter trace-power owner to the ambient matrix trace surface used by the local
  -- smoothness and Hessian computations.
  simp [RealSymmetricMatrixSpace.powerTrace_def]

/-- Helper for Theorem 6.10: the degree-one coefficient-scaled trace-power term is exactly the
local scaled trace continuous linear functional. -/
private lemma coeffMulPowerTraceOne_eq_scaledTrace
    (Φ : AnalyticSymmetricSpectralFunction) :
    (fun Y : SymmMat ↦ Φ.coeff 1 * π[1] Y) =
      fun Y : SymmMat ↦ (((Φ.coeff 1 : ℝ) • traceSymmContinuousLinearMap) Y) := by
  -- Rewrite `π[1]` to the local packaged trace so the affine `k = 1` branch can stay on one
  -- owner spelling.
  funext Y
  calc
    Φ.coeff 1 * π[1] Y = Φ.coeff 1 * Matrix.trace (((Y : Mat)) ^ 1) := by
      rw [powerTrace_eq_ambientTracePow]
    _ = Φ.coeff 1 * traceSymmContinuousLinearMap Y := by
      simp [traceSymmContinuousLinearMap_apply]
    _ = (((Φ.coeff 1 : ℝ) • traceSymmContinuousLinearMap) Y) := by
      simp

/-- Helper for Theorem 6.10: the trace of the square of a symmetric matrix is the sum of the
squares of its ordered eigenvalues. -/
private theorem traceSquare_eq_sum_eigenvalueSquares
    (Q : SymmMat) :
    Matrix.trace (((Q : Mat) ^ (2 : ℕ))) =
      ∑ i : Fin n, (eigenvalues Q i) ^ (2 : ℕ) := by
  -- View the square as the Hermitian functional calculus of the polynomial `x ↦ x²`.
  calc
    Matrix.trace (((Q : Mat) ^ (2 : ℕ)))
        = Matrix.trace (cfc (fun x : ℝ ↦ x ^ (2 : ℕ)) (Q : Mat)) := by
            congr 1
            symm
            simpa using
              cfc_pow_id (Q : Mat) 2 (isHermitian Q : IsSelfAdjoint (Q : Mat))
    _ = Matrix.trace ((isHermitian Q).cfc (fun x : ℝ ↦ x ^ (2 : ℕ))) := by
          rw [(isHermitian Q).cfc_eq]
    _ = ∑ i : Fin n, (eigenvalues Q i) ^ (2 : ℕ) := by
          -- Hermitian functional calculus turns trace into the sum over the ordered eigenvalues.
          rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
            Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
          simp [Function.comp]

/-- Helper for Theorem 6.10: on the exact local `SymmMat` owner used in this file, the
trace-power map `π[k]` is `C²` for every positive exponent. -/
private lemma powerTrace_contDiff_local
    (k : ℕ) (hk : 1 ≤ k) :
    ContDiff ℝ 2 (π[k] : SymmMat → ℝ) := by
  -- Route correction: with the canonical `SymmMat` owner restored, Proposition 6.33's
  -- trace-power regularity theorem is already on the exact surface needed here.
  simpa using powerTrace_contDiff k hk

/-- Helper for Theorem 6.10: multiplying the `k`th trace-power owner by the nonnegative scalar
coefficient `Φ.coeff k` preserves `C²` regularity. -/
lemma coeff_mul_powerTrace_contDiff
    (Φ : AnalyticSymmetricSpectralFunction) (k : ℕ) :
    ContDiff ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) := by
  rcases k with _ | k
  · -- The degree-zero trace-power owner is constant, so the scaled term is `C²`.
    simpa [RealSymmetricMatrixSpace.powerTrace_def] using
      (contDiff_const : ContDiff ℝ 2 (fun _ : SymmMat ↦ Φ.coeff 0 * (n : ℝ)))
  · -- The positive-degree trace-power owner is already `C²`, and scalar multiplication preserves
    -- that regularity.
    have hpowerTrace :
        ContDiff ℝ 2 (π[k + 1] : SymmMat → ℝ) := by
      -- Use the owner-stable local `C²` bridge for positive trace powers.
      have hk1 : 1 ≤ k + 1 := by
        omega
      simpa using powerTrace_contDiff_local (k + 1) hk1
    simpa [smul_eq_mul] using hpowerTrace.const_smul (Φ.coeff (k + 1))

/-- Helper for Theorem 6.10: the Chapter 6.9 trace-power Hessian estimate is reused locally on
the exact `SymmMat` owner surface needed in this file. -/
private theorem powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing_local
    (k : ℕ) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] ≤
      (((k * (k - 1) : ℕ) : ℝ) *
        (∑ i : Fin n,
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
              (k - 2)) *
              (((Matrix.nonneg_iff_posSemidef.mp
                  (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                (2 : ℕ)))) := by
  -- Route correction: the earlier Chapter 6.9 theorem is now available in the current workspace,
  -- so the local estimate can reuse that exact already-proved Hessian bound directly.
  simpa using powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing k X H

/-- Helper for Theorem 6.10: multiplying the `k`th trace-power owner by the nonnegative scalar
coefficient `Φ.coeff k` preserves the Chapter 6.9 Hessian bound. -/
lemma coeff_mul_powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing
    (Φ : AnalyticSymmetricSpectralFunction) {k : ℕ} (hk : 2 ≤ k) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] ≤
      Φ.coeff k *
        ((((k * (k - 1) : ℕ) : ℝ) *
          ∑ i : Fin n,
            (((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
              (k - 2)) *
            (((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                (2 : ℕ)))) := by
  have hpowerCont : ContDiffAt ℝ 2 (π[k] : SymmMat → ℝ) X := by
    exact (powerTrace_contDiff_local k (by omega)).contDiffAt
  have hiter :
      iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] =
        Φ.coeff k * iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] := by
    -- Pull the constant scalar through the second Fréchet derivative before applying the local
    -- Theorem 6.9-style estimate.
    have hsmul :
        iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k • π[k] Y) X =
          Φ.coeff k • iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X :=
      iteratedFDeriv_const_smul_apply' hpowerCont
    simpa [Pi.smul_apply, smul_eq_mul] using congrArg (fun T ↦ T ![H, H]) hsmul
  have hbase :
      iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] ≤
        (((k * (k - 1) : ℕ) : ℝ) *
          ∑ i : Fin n,
            (((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
              (k - 2)) *
              (((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                (2 : ℕ))) := by
    exact powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing_local k X H
  have hcoeff_nonneg : 0 ≤ Φ.coeff k := Φ.coeff_nonneg k hk
  calc
    iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H]
        = Φ.coeff k * iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] := hiter
    _ ≤ Φ.coeff k *
          ((((k * (k - 1) : ℕ) : ℝ) *
            ∑ i : Fin n,
              (((Matrix.nonneg_iff_posSemidef.mp
                  (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                (k - 2)) *
                (((Matrix.nonneg_iff_posSemidef.mp
                    (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                  (2 : ℕ)))) := by
            exact mul_le_mul_of_nonneg_left hbase hcoeff_nonneg

/-- Helper for Theorem 6.10: the degree-zero trace-power owner is constant, so its Hessian
quadratic form vanishes after scaling by `Φ.coeff 0`. -/
lemma coeff_mul_powerTrace_iteratedFDeriv_two_eq_zero_zero
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff 0 * π[0] Y) X ![H, H] = 0 := by
  have hconst :
      (fun Y : SymmMat ↦ Φ.coeff 0 * π[0] Y) = fun _ : SymmMat ↦ Φ.coeff 0 * (n : ℝ) := by
    funext Y
    simp [RealSymmetricMatrixSpace.powerTrace_def]
  -- The degree-zero trace-power owner is constant, so its second derivative vanishes.
  rw [hconst]
  simp [iteratedFDeriv_const_of_ne two_ne_zero (Φ.coeff 0 * (n : ℝ))]

/-- Helper for Theorem 6.10: the degree-one trace-power owner is affine, so its Hessian quadratic
form vanishes after scaling by `Φ.coeff 1`. -/
lemma coeff_mul_powerTrace_iteratedFDeriv_two_eq_zero_one
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff 1 * π[1] Y) X ![H, H] = 0 := by
  let L : SymmMat →L[ℝ] ℝ := (Φ.coeff 1 : ℝ) • traceSymmContinuousLinearMap
  have hcont :
      ContDiffAt ℝ 2 (fun Y : SymmMat ↦ Φ.coeff 1 * π[1] Y) X := by
    -- The degree-one coefficient-scaled trace-power term is a `C²` scalar owner by the earlier
    -- general trace-power regularity lemma.
    exact (coeff_mul_powerTrace_contDiff Φ 1).contDiffAt
  have hslice :
      (fun t : ℝ ↦ Φ.coeff 1 * π[1] (X + t • H)) =
        fun t : ℝ ↦ L X + t * L H := by
    -- Rewrite the degree-one slice through the local continuous trace functional and then use its
    -- linearity to expose an affine scalar function of `t`.
    funext t
    calc
      Φ.coeff 1 * π[1] (X + t • H) = L (X + t • H) := by
        simpa [L] using
          congrArg (fun g : SymmMat → ℝ ↦ g (X + t • H))
            (coeffMulPowerTraceOne_eq_scaledTrace Φ)
      _ = L X + t * L H := by
        exact congrFun (continuousLinearMap_apply_affineLine L X H) t
  have hsliceZero :
      iteratedDeriv 2 (fun t : ℝ ↦ Φ.coeff 1 * π[1] (X + t • H)) 0 = 0 := by
    -- The rewritten slice is affine in `t`, so its second scalar derivative vanishes.
    rw [hslice]
    have hAffineEval :
        iteratedDeriv 2 (fun s : ℝ ↦ L X + s • L H) 0 = 0 := by
      exact congrArg (fun g : ℝ → ℝ ↦ g 0) (affineLineIteratedDerivTwo_generic (L X) (L H))
    simpa [smul_eq_mul] using hAffineEval
  -- Compare the ambient Hessian quadratic form with the affine slice and then use the vanishing
  -- second derivative of the degree-one slice.
  calc
    iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff 1 * π[1] Y) X ![H, H]
        = iteratedDeriv 2 (fun t : ℝ ↦ Φ.coeff 1 * π[1] (X + t • H)) 0 := by
            exact (slice_secondDeriv_eq_iteratedFDeriv_two hcont).symm
    _ = 0 := hsliceZero

/-- Helper for Theorem 6.10: the coefficient-scaled trace-power Hessian bound is valid in every
degree once the low-degree edge cases are reduced to zero. -/
lemma coeff_mul_powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing_all
    (Φ : AnalyticSymmetricSpectralFunction) (k : ℕ) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] ≤
      Φ.coeff k *
        ((((k * (k - 1) : ℕ) : ℝ) *
          ∑ i : Fin n,
            (((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
              (k - 2)) *
              (((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                (2 : ℕ)))) := by
  rcases k with _ | _ | k
  · -- The zero-degree term has zero Hessian and the right-hand side also vanishes.
    rw [coeff_mul_powerTrace_iteratedFDeriv_two_eq_zero_zero]
    simp
  · -- The degree-one term is affine, so the Hessian again vanishes.
    rw [coeff_mul_powerTrace_iteratedFDeriv_two_eq_zero_one]
    simp
  · -- Every higher degree is covered by the coefficient-scaled version of Theorem 6.9.
    exact coeff_mul_powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing Φ (by omega) X H

/-- Helper for Theorem 6.10: the Proposition 6.33 mixed summand can be rewritten in the sandwich
trace form used by the absolute-value comparison step. -/
private abbrev mixedTraceTerm
    (k p : ℕ) (X H : SymmMat) : ℝ :=
  ((((X : Mat)).transpose ^ (k - 2 - p)) *
      (((H : Mat)).transpose * ((((X : Mat)).transpose ^ p) * (H : Mat)))).trace

/-- Helper for Theorem 6.10: this is the same mixed summand written in the intrinsic
`X ^ p · H · X ^ (k - 2 - p)` sandwich spelling. -/
private abbrev sandwichTraceTerm
    (k p : ℕ) (X H : SymmMat) : ℝ :=
  Matrix.trace
    (((((X ^ p : SymmMat) : Mat) * (H : Mat) *
        ((X ^ (k - 2 - p) : SymmMat) : Mat)).transpose) * (H : Mat))

/-- Helper for Theorem 6.10: the Proposition 6.33 mixed summand is exactly the sandwich trace
term once the symmetry of `X` and `H` is used. -/
private theorem mixedTraceTermEqSandwichTraceTerm
    (k p : ℕ) (X H : SymmMat) :
    mixedTraceTerm k p X H = sandwichTraceTerm k p X H := by
  -- Expand both trace formulas and use symmetry to align the ambient matrix factors.
  simp [mixedTraceTerm, sandwichTraceTerm, Matrix.mul_assoc,
    RealSymmetricMatrixSpace.coe_pow, (RealSymmetricMatrixSpace.isSymm X).eq,
    (RealSymmetricMatrixSpace.isSymm H).eq]

/-- Helper for Theorem 6.10: the ordered eigenvalues of the intrinsic absolute value `|X|` agree
with the ordered ambient Hermitian eigenvalues of `CFC.abs X`. -/
private theorem absEigenvaluesEqAmbientAbsEigenvalues
    (X : SymmMat) :
    eigenvalues (|X| : SymmMat) =
      (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues := by
  have habsHerm : (CFC.abs (X : Mat)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian
  -- Compare the two Hermitian owners through the shared ambient matrix `CFC.abs X`.
  exact
    ((habsHerm.eigenvalues_eq_eigenvalues_iff (isHermitian (|X| : SymmMat))).2 <| by
      simp [RealSymmetricMatrixSpace.coe_abs]).symm

/-- Helper for Theorem 6.10: the trace of `H²` is the sum of the squared ambient absolute-value
eigenvalues of `H`. -/
private theorem traceSquare_eq_ambientAbsEigenvalueSquares
    (H : SymmMat) :
    Matrix.trace (((H ^ (2 : ℕ) : SymmMat) : Mat)) =
      ∑ i : Fin n,
        (((Matrix.nonneg_iff_posSemidef.mp
            (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i) ^ (2 : ℕ)) := by
  have hAbsSq :
      star (H : Mat) * (H : Mat) = CFC.abs (H : Mat) * CFC.abs (H : Mat) := by
    have hpow := CFC.nnrpow_two (CFC.abs (H : Mat))
    exact (CFC.abs_nnrpow_two (H : Mat)).symm.trans hpow
  have hmat :
      (((H ^ (2 : ℕ) : SymmMat) : Mat)) = (((|H| : SymmMat) : Mat) ^ (2 : ℕ)) := by
    -- Rewrite `H²` to `|H|²` through the ambient functional-calculus identity `|H|² = Hᵀ H`.
    calc
      (((H ^ (2 : ℕ) : SymmMat) : Mat)) = (H : Mat) * (H : Mat) := by
        simp [RealSymmetricMatrixSpace.coe_pow, pow_two]
      _ = star (H : Mat) * (H : Mat) := by
        rw [show star (H : Mat) = (H : Mat) by
          simpa using (RealSymmetricMatrixSpace.isHermitian H).eq]
      _ = CFC.abs (H : Mat) * CFC.abs (H : Mat) := hAbsSq
      _ = (CFC.abs (H : Mat)) ^ (2 : ℕ) := by
        simp [pow_two]
      _ = (((|H| : SymmMat) : Mat) ^ (2 : ℕ)) := by
        simp [RealSymmetricMatrixSpace.coe_abs]
  calc
    Matrix.trace (((H ^ (2 : ℕ) : SymmMat) : Mat))
        = Matrix.trace ((((|H| : SymmMat) : Mat) ^ (2 : ℕ))) := by
            rw [hmat]
    _ = ∑ i : Fin n, (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ) := by
          simpa using traceSquare_eq_sum_eigenvalueSquares (|H| : SymmMat)
    _ = ∑ i : Fin n,
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i) ^ (2 : ℕ)) := by
          simp [absEigenvaluesEqAmbientAbsEigenvalues]

/-- Helper for Theorem 6.10: the all-degree coefficient-scaled trace-power bound can be rewritten
from the ambient `CFC.abs` eigenvalue surface to the intrinsic `eigenvalues (|X|)` surface used in
the theorem statement. -/
lemma coeff_mul_powerTrace_iteratedFDeriv_two_le_intrinsicAbsEigenvaluePairing
    (Φ : AnalyticSymmetricSpectralFunction) (k : ℕ) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] ≤
      Φ.coeff k *
        ((((k * (k - 1) : ℕ) : ℝ) *
          ∑ i : Fin n,
            (eigenvalues (|X| : SymmMat) i) ^ (k - 2) *
              (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ))) := by
  -- Rewrite the ambient Hermitian eigenvalue vectors from the all-degree coefficient estimate
  -- into the intrinsic absolute-value eigenvalue vectors used on the theorem surface.
  simpa [absEigenvaluesEqAmbientAbsEigenvalues] using
    coeff_mul_powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing_all Φ k X H

/-- Helper for Theorem 6.10: along the affine line `t ↦ X + t • H`, the scalar second derivative
of `Φ.matrixFun` at `0` is exactly the ambient Hessian quadratic form in the direction `H`. -/
lemma slice_secondDeriv_eq_hessianQuadraticForm
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat)
    (hcont : ContDiffAt ℝ 2 Φ.matrixFun X) :
    iteratedDeriv 2 (fun t : ℝ ↦ Φ.matrixFun (X + t • H)) 0 =
      (iteratedFDeriv ℝ 2 Φ.matrixFun X) ![H, H] := by
  -- The scalar affine slice records the Hessian quadratic form in the repeated direction `H`.
  exact slice_secondDeriv_eq_iteratedFDeriv_two hcont

/-- Helper for Theorem 6.10: the degree-zero trace-power owner `π[0]` is the constant scalar `n`.
-/
lemma powerTrace_zero_eq_card
    (X : SymmMat) :
    π[0] X = n := by
  simp [RealSymmetricMatrixSpace.powerTrace_def]

/-- Helper for Theorem 6.10: a scalar belongs to `Φ.scalarDom` exactly when its norm lies
strictly below the convergence radius. -/
lemma mem_scalarDom_iff
    (Φ : AnalyticSymmetricSpectralFunction) {τ : ℝ} :
    τ ∈ Φ.scalarDom ↔ ENNReal.ofReal ‖τ‖ < Φ.radius := by
  -- Unfold the scalar-domain `eball` and rewrite the extended distance on `ℝ` as the norm.
  change edist τ 0 < Φ.radius ↔ ENNReal.ofReal ‖τ‖ < Φ.radius
  have hnorm : ‖τ‖ₑ = ENNReal.ofReal ‖τ‖ := by
    simpa [Real.norm_eq_abs] using
      (Real.enorm_eq_ofReal (abs_nonneg τ) : ‖|τ|‖ₑ = ENNReal.ofReal |τ|)
  rw [edist_zero_right, hnorm]

/-- Helper for Theorem 6.10: domain membership gives the scalar-radius bound on each ordered
eigenvalue directly. -/
lemma eigenvalue_norm_lt_radius_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X : SymmMat) (hX : X ∈ Φ.dom) (i : Fin n) :
    ENNReal.ofReal ‖eigenvalues X i‖ < Φ.radius := by
  -- Route correction: the previous Frobenius-norm helper was too strong. The domain hypothesis
  -- controls the eigenvalues coordinatewise, and that is the exact scalar-domain fact available
  -- without an additional operator-vs-Frobenius norm bridge.
  rw [AnalyticSymmetricSpectralFunction.mem_dom_iff] at hX
  simpa [mem_scalarDom_iff] using hX i

/-- Helper for Theorem 6.10: membership in the centered interval `(-ε, ε)` is equivalent to the
absolute-value bound needed by the slice-domain hypothesis. -/
lemma abs_lt_of_mem_centeredInterval {ε t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) :
    |t| < ε := by
  -- Repackage the interval inequalities in the symmetric `abs_lt` form.
  exact abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩

/-- Helper for Theorem 6.10: membership in the centered interval `(-ε, ε)` is equivalent to the
absolute-value bound `|t| < ε`. -/
private lemma mem_centeredInterval_iff_abs_lt {ε t : ℝ} :
    t ∈ Set.Ioo (-ε) ε ↔ |t| < ε := by
  constructor
  · intro ht
    exact abs_lt_of_mem_centeredInterval ht
  · intro ht
    exact abs_lt.mp ht

/-- Helper for Theorem 6.10: if `ε > 0`, then `0` lies in the centered interval `(-ε, ε)`. -/
lemma zero_mem_centeredInterval {ε : ℝ} (hε : 0 < ε) :
    (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
  -- Record the interval-membership side condition needed later for `derivWithin_tsum` at `0`.
  constructor <;> linarith

/-- Helper for Theorem 6.10: on the small interval where the affine slice stays inside `Φ.dom`,
the scalar slice inherits the pointwise trace-power `HasSum` expansion from `Φ.matrixFun`. -/
lemma matrixFunSlice_hasSum_powerTraceOnInterval
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ : ℝ}
    (hslice :
      ∀ ⦃t : ℝ⦄, |t| < ε → X + t • H ∈ Φ.dom ∧ ‖(X + t • H : SymmMat)‖ < ρ) :
    ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo (-ε) ε →
      HasSum (fun k : ℕ ↦ Φ.coeff k * π[k] (X + t • H)) (Φ.matrixFun (X + t • H)) := by
  intro t ht
  -- The interval hypothesis gives the slice-domain witness, so the pointwise series expansion
  -- of `Φ.matrixFun` applies directly at `X + t • H`.
  have htabs : |t| < ε := (mem_centeredInterval_iff_abs_lt).mp ht
  exact Φ.matrixFun_hasSum_powerTrace ((hslice htabs).1)

/-- Helper for Theorem 6.10: on the centered interval where the affine slice stays inside
`Φ.dom`, the trace-power `tsum` itself agrees pointwise with the source-facing slice
`t ↦ Φ.matrixFun (X + t • H)`. -/
lemma matrixFunSlice_tsum_eqOnInterval
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ : ℝ}
    (hslice :
      ∀ ⦃t : ℝ⦄, |t| < ε → X + t • H ∈ Φ.dom ∧ ‖(X + t • H : SymmMat)‖ < ρ) :
    Set.EqOn
      (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
      (fun t : ℝ ↦ Φ.matrixFun (X + t • H))
      (Set.Ioo (-ε) ε) := by
  -- Package the pointwise `HasSum` expansion into an `EqOn` rewrite surface for later
  -- `derivWithin_tsum` applications.
  intro t ht
  exact (matrixFunSlice_hasSum_powerTraceOnInterval Φ X H hslice ht).tsum_eq

/-- Helper for Theorem 6.10: because the centered slice interval is open, the pointwise
trace-power expansion of `Φ.matrixFun` on that interval remains valid after taking iterated scalar
derivatives. -/
lemma matrixFunSlice_iteratedDeriv_eqOnInterval
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ : ℝ}
    (hslice :
      ∀ ⦃t : ℝ⦄, |t| < ε → X + t • H ∈ Φ.dom ∧ ‖(X + t • H : SymmMat)‖ < ρ)
    (m : ℕ) :
    Set.EqOn
      (fun t : ℝ ↦
        iteratedDeriv m (fun s : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + s • H)) t)
      (fun t : ℝ ↦ iteratedDeriv m (fun s : ℝ ↦ Φ.matrixFun (X + s • H)) t)
      (Set.Ioo (-ε) ε) := by
  -- Differentiate the open-interval slice expansion on both sides without leaving the same
  -- centered interval.
  simpa using
    Set.EqOn.iteratedDeriv_of_isOpen
      (matrixFunSlice_tsum_eqOnInterval Φ X H hslice)
      isOpen_Ioo
      m

/-- Helper for Theorem 6.10: the open-interval slice expansion stays valid after taking the
second scalar derivative, which is the exact normalization needed for the theorem body. -/
lemma matrixFunSlice_iteratedDerivTwo_eqOnInterval
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ : ℝ}
    (hslice :
      ∀ ⦃t : ℝ⦄, |t| < ε → X + t • H ∈ Φ.dom ∧ ‖(X + t • H : SymmMat)‖ < ρ) :
    Set.EqOn
      (fun t : ℝ ↦ iteratedDeriv 2 (fun s : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + s • H)) t)
      (fun t : ℝ ↦ iteratedDeriv 2 (fun s : ℝ ↦ Φ.matrixFun (X + s • H)) t)
      (Set.Ioo (-ε) ε) := by
  -- Specialize the general iterated-derivative transport lemma to the second derivative.
  simpa using matrixFunSlice_iteratedDeriv_eqOnInterval
    Φ X H hslice 2

/-- Helper for Theorem 6.10: after one scalar derivative, evaluating the resulting derivative
power series at `1` turns its `(n + 1)`st scalar coefficient into `(n + 2) * a_{n+2}`. -/
lemma scalar_derivSeries_coeff_succ
    (Φ : AnalyticSymmetricSpectralFunction) (n : ℕ) :
    let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ Φ.coeff
    let eval1 : (ℝ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)
    (eval1.compFormalMultilinearSeries p.derivSeries).coeff (n + 1) =
      ((n + 2 : ℝ) * Φ.coeff (n + 2)) := by
  have hnat : n + 1 + 1 = n + 2 := by
    simp [Nat.add_assoc]
  -- Evaluate the first derivative-series coefficient at `1` and rewrite it back to the
  -- scalar coefficient sequence of `Φ`.
  dsimp
  change (((FormalMultilinearSeries.ofScalars ℝ Φ.coeff).derivSeries).coeff (n + 1)) 1 =
    ((n + 2 : ℝ) * Φ.coeff (n + 2))
  simp [FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars, hnat, nsmul_eq_mul]

/-- Helper for Theorem 6.10: after differentiating the scalar series once, evaluating the
derivative-series terms at `1` gives a convergent series for the scalar derivative on
`Φ.scalarDom`. -/
lemma scalar_firstDerivSeries_hasSum
    (Φ : AnalyticSymmetricSpectralFunction) {τ : ℝ} (hτ : τ ∈ Φ.scalarDom) :
    let f : ℝ → ℝ := FormalMultilinearSeries.ofScalarsSum Φ.coeff
    let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ Φ.coeff
    let eval1 : (ℝ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)
    let p1 : FormalMultilinearSeries ℝ ℝ ℝ := eval1.compFormalMultilinearSeries p.derivSeries
    HasSum (fun n : ℕ ↦ p1 n fun _ ↦ τ) (deriv f τ) := by
  dsimp
  have hderiv :
      HasFPowerSeriesOnBall
        (fderiv ℝ (FormalMultilinearSeries.ofScalarsSum Φ.coeff))
        (FormalMultilinearSeries.ofScalars ℝ Φ.coeff).derivSeries
        0
        Φ.radius := by
    simpa using Φ.hasFPowerSeriesOnBall.fderiv
  -- Apply the scalar evaluation map to the derivative power series and identify the resulting sum
  -- with the one-dimensional derivative.
  simpa [fderiv_apply_one_eq_deriv] using
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasSum (hderiv.hasSum hτ)

/-- Helper for Theorem 6.10: the `n`th scalar first-derivative series term is exactly
`(n + 1) a_{n+1} τ^n`. -/
lemma scalar_firstDerivSeries_term_eq
    (Φ : AnalyticSymmetricSpectralFunction) (τ : ℝ) (n : ℕ) :
    let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ Φ.coeff
    let eval1 : (ℝ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)
    let p1 : FormalMultilinearSeries ℝ ℝ ℝ := eval1.compFormalMultilinearSeries p.derivSeries
    p1 n (fun _ ↦ τ) =
      τ ^ n * (((n + 1 : ℕ) : ℝ) * Φ.coeff (n + 1)) := by
  -- Unfold the once-derived scalar series and evaluate its multilinear term on the diagonal.
  dsimp
  simp [FormalMultilinearSeries.derivSeries_coeff_one, smul_eq_mul]

/-- Helper for Theorem 6.10: after removing the low-degree branch, the shifted scalar
first-derivative coefficient series is summable on the scalar convergence domain. -/
lemma scalarFirstDerivSeries_summable_shifted
    (Φ : AnalyticSymmetricSpectralFunction) {ρ : ℝ} (hρ : ρ ∈ Φ.scalarDom) :
    Summable (fun n : ℕ ↦ Φ.coeff (n + 2) * (((n + 2 : ℕ) : ℝ) * ρ ^ (n + 1))) := by
  have hsum := (scalar_firstDerivSeries_hasSum (Φ := Φ) hρ).summable
  have hshift := (summable_nat_add_iff 1).2 hsum
  -- Shift the convergent first-derivative series by one step and rewrite the shifted term
  -- into the normalized coefficient shape used later in the tail estimates.
  simpa [scalar_firstDerivSeries_term_eq, Nat.add_assoc, mul_assoc, mul_left_comm, mul_comm]
    using hshift
/-- Helper for Theorem 6.10: after differentiating the scalar series twice, the remaining
Fréchet derivative at `τ` is still represented by the second derivative-series before the final
evaluation at `1`. -/
lemma scalar_secondDerivSeries_hasSum
    (Φ : AnalyticSymmetricSpectralFunction) {τ : ℝ} (hτ : τ ∈ Φ.scalarDom) :
    let f : ℝ → ℝ := FormalMultilinearSeries.ofScalarsSum Φ.coeff
    let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ Φ.coeff
    let eval1 : (ℝ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)
    let p1 : FormalMultilinearSeries ℝ ℝ ℝ := eval1.compFormalMultilinearSeries p.derivSeries
    HasSum (fun n : ℕ ↦ eval1 ((p1.derivSeries n) fun _ ↦ τ))
      ((fderiv ℝ (deriv f) τ) 1) := by
  dsimp
  have hderiv :
      HasFPowerSeriesOnBall
        (fderiv ℝ (FormalMultilinearSeries.ofScalarsSum Φ.coeff))
        (FormalMultilinearSeries.ofScalars ℝ Φ.coeff).derivSeries
        0
        Φ.radius := by
    simpa using Φ.hasFPowerSeriesOnBall.fderiv
  have hfirst :
      HasFPowerSeriesOnBall
        (deriv (FormalMultilinearSeries.ofScalarsSum Φ.coeff))
        ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compFormalMultilinearSeries
          (FormalMultilinearSeries.ofScalars ℝ Φ.coeff).derivSeries)
        0
        Φ.radius := by
    simpa [fderiv_apply_one_eq_deriv] using
      (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp_hasFPowerSeriesOnBall hderiv
  have hsecond :
      HasFPowerSeriesOnBall
        (fderiv ℝ (deriv (FormalMultilinearSeries.ofScalarsSum Φ.coeff)))
        (((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compFormalMultilinearSeries
            (FormalMultilinearSeries.ofScalars ℝ Φ.coeff).derivSeries).derivSeries)
        0
        Φ.radius := by
    simpa using hfirst.fderiv
  -- Apply the scalar evaluation map to the once-more differentiated power series.
  simpa using
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasSum (hsecond.hasSum hτ)
/-- Helper for Theorem 6.10: evaluating the `n`th term of the second derivative-series at `1`
recovers the shifted coefficient `(n + 1)(n + 2) a_{n+2}`. -/
lemma scalar_secondDerivSeries_term_eq
    (Φ : AnalyticSymmetricSpectralFunction) (τ : ℝ) (n : ℕ) :
    let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ Φ.coeff
    let eval1 : (ℝ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)
    let p1 : FormalMultilinearSeries ℝ ℝ ℝ := eval1.compFormalMultilinearSeries p.derivSeries
    eval1 ((p1.derivSeries n) fun _ ↦ τ) =
      τ ^ n * ((((n + 1) * (n + 2) : ℕ) : ℝ) * Φ.coeff (n + 2)) := by
  -- Unfold the twice-derived scalar term, then rewrite the once-derived coefficient with the
  -- owner-level coefficient formula from `scalar_derivSeries_coeff_succ`.
  dsimp
  simp [FormalMultilinearSeries.derivSeries_coeff_one, scalar_derivSeries_coeff_succ,
    smul_eq_mul, mul_assoc]
/-- Helper for Theorem 6.10: on the scalar convergence domain, `iteratedDeriv 2 Φ` is exactly
the resummed second derivative-series coming from the scalar power series of `Φ`. -/
lemma iteratedDeriv_two_eq_scalarSecondDerivSeries
    (Φ : AnalyticSymmetricSpectralFunction) {τ : ℝ} (hτ : τ ∈ Φ.scalarDom) :
    iteratedDeriv 2 Φ τ =
      ∑' n : ℕ, τ ^ n * ((((n + 1) * (n + 2) : ℕ) : ℝ) * Φ.coeff (n + 2)) := by
  have hsum := scalar_secondDerivSeries_hasSum (Φ := Φ) (τ := τ) hτ
  have hrewrite :
      HasSum
        (fun n : ℕ ↦ τ ^ n * ((((n + 1) * (n + 2) : ℕ) : ℝ) * Φ.coeff (n + 2)))
        ((fderiv ℝ (deriv Φ) τ) 1) := by
    -- Rewrite the owner-level twice-differentiated formal series into the scalar coefficient
    -- normal form used throughout the Hessian majorant.
    convert hsum using 1
    ext n
    symm
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (scalar_secondDerivSeries_term_eq (Φ := Φ) τ n)
  -- The Fréchet derivative of `deriv Φ` evaluated at `1` is exactly `iteratedDeriv 2 Φ τ`.
  calc
    iteratedDeriv 2 Φ τ = (fderiv ℝ (deriv Φ) τ) 1 := by
      simp [iteratedDeriv_succ]
    _ = ∑' n : ℕ, τ ^ n * ((((n + 1) * (n + 2) : ℕ) : ℝ) * Φ.coeff (n + 2)) := by
      symm
      exact hrewrite.tsum_eq
/-- Helper for Theorem 6.10: the scalar second derivative is also the convergent shifted series
with coefficient shape `a_k * k (k - 1) * τ^(k - 2)` that appears after the termwise Hessian
estimate for the trace-power summands. -/
lemma scalarSecondDerivSeries_hasSum_shifted
    (Φ : AnalyticSymmetricSpectralFunction) {τ : ℝ} (hτ : τ ∈ Φ.scalarDom) :
    HasSum
      (fun k : ℕ ↦
        Φ.coeff k * ((((k * (k - 1) : ℕ) : ℝ) * τ ^ (k - 2))))
      (iteratedDeriv 2 Φ τ) := by
  let f : ℕ → ℝ := fun k ↦
    Φ.coeff k * ((((k * (k - 1) : ℕ) : ℝ) * τ ^ (k - 2)))
  have hnorm :
      HasSum
        (fun n : ℕ ↦ τ ^ n * ((((n + 1) * (n + 2) : ℕ) : ℝ) * Φ.coeff (n + 2)))
        (iteratedDeriv 2 Φ τ) := by
    -- Record the normalized scalar second-derivative series as a `HasSum`.
    have hsum := scalar_secondDerivSeries_hasSum (Φ := Φ) (τ := τ) hτ
    have hrewrite :
        HasSum
          (fun n : ℕ ↦ τ ^ n * ((((n + 1) * (n + 2) : ℕ) : ℝ) * Φ.coeff (n + 2)))
          ((fderiv ℝ (deriv Φ) τ) 1) := by
      convert hsum using 1
      ext n
      symm
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (scalar_secondDerivSeries_term_eq (Φ := Φ) τ n)
    simpa [iteratedDeriv_succ] using hrewrite
  have htail : HasSum (fun n : ℕ ↦ f (n + 2)) (iteratedDeriv 2 Φ τ) := by
    -- Reindex the normalized coefficients into the source-facing shifted form `k (k - 1) a_k`.
    convert hnorm using 1
    ext n
    simp [f, mul_assoc, mul_left_comm, mul_comm]
  have hhead : ∑ i ∈ Finset.range 2, f i = 0 := by
    -- The `k = 0, 1` head terms vanish because of the explicit factor `k (k - 1)`.
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [f]
  have htail_zero :
      HasSum (fun n : ℕ ↦ f (n + 2))
        (iteratedDeriv 2 Φ τ - ∑ i ∈ Finset.range 2, f i) := by
    simpa [hhead] using htail
  -- Add back the zero head terms to recover the full shifted coefficient series.
  simpa [f] using (hasSum_nat_add_iff' 2).1 htail_zero
/-- Helper for Theorem 6.10: matrix-domain membership forces every intrinsic absolute eigenvalue
of `X` to lie in the scalar convergence domain `Φ.scalarDom`. -/
lemma intrinsicAbsEigenvalues_mem_scalarDom_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X : SymmMat) (hX : X ∈ Φ.dom) :
    ∀ i : Fin n, eigenvalues (|X| : SymmMat) i ∈ Φ.scalarDom := by
  intro i
  have habs_nonneg : 0 ≤ eigenvalues (|X| : SymmMat) i := by
    -- The intrinsic absolute value is positive semidefinite, so its eigenvalues are nonnegative.
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (RealSymmetricMatrixSpace.abs_nonneg X)).eigenvalues_nonneg i
  have hself : IsSelfAdjoint (X : Mat) := by
    simpa using (isHermitian X)
  have hrange :
      Set.range (eigenvalues (|X| : SymmMat)) =
        (fun z : ℝ ↦ ‖z‖) '' Set.range (eigenvalues X) := by
    -- Identify the spectrum of `|X|` with the absolute-value image of the spectrum of `X`.
    calc
      Set.range (eigenvalues (|X| : SymmMat))
          = spectrum ℝ (((|X| : SymmMat) : Mat)) := by
              symm
              rw [(isHermitian (|X| : SymmMat)).spectrum_real_eq_range_eigenvalues]
      _ = spectrum ℝ (CFC.abs (X : Mat)) := by
            simp [RealSymmetricMatrixSpace.coe_abs]
      _ = (fun z : ℝ ↦ ‖z‖) '' spectrum ℝ (X : Mat) := by
            simpa using (CFC.spectrum_abs (X : Mat) hself)
      _ = (fun z : ℝ ↦ ‖z‖) '' Set.range (eigenvalues X) := by
            rw [(isHermitian X).spectrum_real_eq_range_eigenvalues]
  have hi :
      eigenvalues (|X| : SymmMat) i ∈
        (fun z : ℝ ↦ ‖z‖) '' Set.range (eigenvalues X) := by
    rw [← hrange]
    exact ⟨i, rfl⟩
  rcases hi with ⟨y, ⟨j, rfl⟩, hy⟩
  -- Transfer the radius bound from the original eigenvalue to the matching absolute eigenvalue.
  rw [mem_scalarDom_iff]
  have hj := eigenvalue_norm_lt_radius_of_mem_dom (Φ := Φ) X hX j
  simpa [hy, Real.norm_eq_abs, abs_of_nonneg habs_nonneg] using hj
/-- Helper for Theorem 6.10: once the intrinsic absolute eigenvalues of `X` lie in
`Φ.scalarDom`, the coefficient series on the theorem's right-hand side resums to the claimed
finite spectral sum. -/
lemma hasSum_intrinsicAbsEigenvalueSquareSeries
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat)
    (habsX : ∀ i : Fin n, eigenvalues (|X| : SymmMat) i ∈ Φ.scalarDom) :
    HasSum
      (fun k : ℕ ↦
        Φ.coeff k *
          ((((k * (k - 1) : ℕ) : ℝ) *
            ∑ i : Fin n,
              (eigenvalues (|X| : SymmMat) i) ^ (k - 2) *
                (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ))))
      (∑ i : Fin n,
        iteratedDeriv 2 Φ (eigenvalues (|X| : SymmMat) i) *
          (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ)) := by
  have hscalar :
      ∀ i : Fin n,
        HasSum
          (fun k : ℕ ↦
            Φ.coeff k *
              ((((k * (k - 1) : ℕ) : ℝ) * (eigenvalues (|X| : SymmMat) i) ^ (k - 2)) *
                (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ)))
          (iteratedDeriv 2 Φ (eigenvalues (|X| : SymmMat) i) *
            (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ)) := by
    intro i
    -- Resum the scalar second derivative at each eigenvalue of `|X|`, then scale by the fixed
    -- squared eigenvalue of `|H|`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (scalarSecondDerivSeries_hasSum_shifted
        (Φ := Φ) (τ := eigenvalues (|X| : SymmMat) i) (hτ := habsX i)).mul_right
        ((eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ))
  have hpartial :
      ∀ s : Finset (Fin n),
        HasSum
          (fun k : ℕ ↦
            s.sum (fun i ↦
              Φ.coeff k *
                ((((k * (k - 1) : ℕ) : ℝ) * (eigenvalues (|X| : SymmMat) i) ^ (k - 2)) *
                  (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ))))
          (s.sum fun i ↦
            iteratedDeriv 2 Φ (eigenvalues (|X| : SymmMat) i) *
              (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi hs
      -- Assemble the finite spectral sum by adding one scalar eigenvalue series at a time.
      simpa [Finset.sum_insert, hi, add_comm, add_left_comm, add_assoc] using (hscalar i).add hs
  have hsum := hpartial Finset.univ
  -- Factor the common coefficient `Φ.coeff k` back out of the finite spectral sum.
  convert hsum using 1
  ext k
  let c : ℝ := (((k * (k - 1) : ℕ) : ℝ))
  let u : Fin n → ℝ := fun i ↦
    (eigenvalues (|X| : SymmMat) i) ^ (k - 2) * (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ)
  -- Normalize both sides to the same double factored finite sum.
  simp [Finset.mul_sum, mul_assoc, mul_comm]
section L2OperatorSlice

open scoped Matrix.Norms.L2Operator

attribute [local instance 3000] Matrix.instL2OpMetricSpace
attribute [local instance 3000] Matrix.instL2OpNormedAddCommGroup
attribute [local instance 3000] Matrix.instL2OpNormedSpace
attribute [local instance 3000] Matrix.instL2OpNormedRing
attribute [local instance 3000] Matrix.instL2OpNormedAlgebra
attribute [local instance 3000] Matrix.instCStarRing

/-- Helper for Theorem 6.10: the ambient `L²` operator norm of the identity matrix is at most
`1`, which is the only base-case estimate needed for later power-norm inductions. -/
private theorem ambientOpNorm_one_le_one :
    ambientOpNorm (1 : Mat) ≤ (1 : ℝ) := by
  -- Diagonal matrices have `L²` operator norm equal to the `π`-norm of their diagonal entries.
  rw [ambientOpNorm, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (show 0 ≤ (1 : ℝ) by positivity)).2 fun _ ↦ by simp

/-- Helper for Theorem 6.10: domain membership forces the ambient Euclidean operator norm of the
underlying symmetric matrix to stay strictly below the scalar convergence radius. -/
lemma opNorm_lt_radius_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X : SymmMat) (hX : X ∈ Φ.dom) :
    ENNReal.ofReal ‖((X : Mat))‖ < Φ.radius := by
  by_cases hrad : Φ.radius = ⊤
  · -- If the scalar radius is infinite, every finite operator norm is automatically admissible.
    simpa [hrad] using Φ.radius_pos
  by_cases hne : Nonempty (Fin n)
  · letI := hne
    let hHerm : (X : Mat).IsHermitian := RealSymmetricMatrixSpace.isHermitian X
    let U : Matrix.unitaryGroup (Fin n) ℝ := hHerm.eigenvectorUnitary
    have hdiagNorm :
        ‖((X : Mat))‖ = ‖WithLp.toLp (⊤ : ENNReal) (eigenvalues X)‖ := by
      -- Diagonalize the symmetric matrix in its eigenbasis and read off the diagonal operator norm.
      calc
        ‖((X : Mat))‖ = ‖star (U : Mat) * (X : Mat) * (U : Mat)‖ := by
            symm
            simpa [U] using unitaryConj_l2OperatorNorm_eq U (X : Mat)
        _ = ‖Matrix.diagonal (eigenvalues X)‖ := by
            congr 1
            simpa [U] using hHerm.conjStarAlgAut_star_eigenvectorUnitary
        _ = ‖WithLp.toLp (⊤ : ENNReal) (eigenvalues X)‖ := by
            simpa using Matrix.l2_opNorm_diagonal (v := eigenvalues X)
    have hrad_toReal_pos : 0 < Φ.radius.toReal :=
      ENNReal.toReal_pos (ne_of_gt Φ.radius_pos) hrad
    have hcoord :
        ∀ i : Fin n, ‖eigenvalues X i‖ < Φ.radius.toReal := by
      intro i
      -- Convert the coordinatewise domain bound from `ENNReal` back to a real inequality.
      exact
        (ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) hrad).1
          (eigenvalue_norm_lt_radius_of_mem_dom (Φ := Φ) X hX i)
    have hnorm_lt :
        ‖WithLp.toLp (⊤ : ENNReal) (eigenvalues X)‖ < Φ.radius.toReal := by
      -- The `ℓ∞` norm is strictly below the radius once every coordinate is.
      simpa using (pi_norm_lt_iff hrad_toReal_pos).2 hcoord
    -- Transport the real operator-norm bound back to the extended-real radius inequality.
    exact
      (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hrad).2 <| by
        simpa [hdiagNorm] using hnorm_lt
  · letI : IsEmpty (Fin n) := not_nonempty_iff.mp hne
    -- In dimension `0`, the ambient matrix norm vanishes, so strict positivity of the radius is enough.
    simpa using Φ.radius_pos
/-- Helper for Theorem 6.10: an operator-norm bound strictly below a scalar witness in
`Φ.scalarDom` keeps the whole symmetric matrix in `Φ.dom`. -/
private lemma dom_of_opNorm_lt_scalarWitness
    (Φ : AnalyticSymmetricSpectralFunction) {Y : SymmMat} {ρ : ℝ}
    (hρ : ρ ∈ Φ.scalarDom) (hY : ambientOpNorm (Y : Mat) < ρ) :
    Y ∈ Φ.dom := by
  rw [AnalyticSymmetricSpectralFunction.mem_dom_iff]
  intro i
  letI : Nonempty (Fin n) := ⟨i⟩
  rw [mem_scalarDom_iff]
  have hρ_nonneg : 0 ≤ ρ := le_trans (by simpa [ambientOpNorm] using norm_nonneg (Y : Mat)) hY.le
  have hiSpec : eigenvalues Y i ∈ spectrum ℝ ((Y : Mat)) := by
    -- Each ordered eigenvalue is an ambient real spectral value of the symmetric matrix.
    rw [(RealSymmetricMatrixSpace.isHermitian Y).spectrum_real_eq_range_eigenvalues]
    exact ⟨i, rfl⟩
  have hi_le : ‖eigenvalues Y i‖ ≤ ‖((Y : Mat))‖ := by
    exact spectrum.norm_le_norm_of_mem hiSpec
  have hi_lt : ‖eigenvalues Y i‖ < ρ := lt_of_le_of_lt hi_le (by simpa [ambientOpNorm] using hY)
  have hi_enn : ENNReal.ofReal ‖eigenvalues Y i‖ < ENNReal.ofReal ρ := by
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).2 hi_lt
  have hρ_enn : ENNReal.ofReal ρ < Φ.radius := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hρ_nonneg] using (mem_scalarDom_iff (Φ := Φ)).1 hρ
  exact hi_enn.trans hρ_enn
/-- Helper for Theorem 6.10: every domain point admits a scalar-radius witness strictly above its
ambient Euclidean operator norm. This isolates the neighborhood data later used to compare
`Φ.matrixFun` with its trace-power `tsum`. -/
private lemma exists_scalarWitness_gt_opNorm_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X : SymmMat) (hX : X ∈ Φ.dom) :
    ∃ ρ : ℝ, ambientOpNorm (X : Mat) < ρ ∧ ρ ∈ Φ.scalarDom := by
  have hop : ENNReal.ofReal (ambientOpNorm (X : Mat)) < Φ.radius := by
    simpa [ambientOpNorm] using opNorm_lt_radius_of_mem_dom (Φ := Φ) X hX
  obtain ⟨ρ, hρ_nonneg, hXρ, hρrad⟩ := ENNReal.lt_iff_exists_real_btwn.1 hop
  refine ⟨ρ, ?_, ?_⟩
  · -- Convert the ENNReal gap back to a strict real inequality above the operator norm.
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by simpa [ambientOpNorm] using norm_nonneg (X : Mat))).1 hXρ
  · -- The interpolating real witness lies in the scalar convergence interval.
    rw [mem_scalarDom_iff]
    simpa [Real.norm_eq_abs, abs_of_nonneg hρ_nonneg] using hρrad
/-- Helper for Theorem 6.10: at any matrix-domain point, the shifted trace-power tail
`m ↦ Φ.coeff (m + 2) * π[m + 2] X` is summable because it is just the degree-`≥ 2` tail of the
already convergent trace-power expansion of `Φ.matrixFun X`. -/
private lemma powerTrace_tail_summable_at_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X : SymmMat) (hX : X ∈ Φ.dom) :
    Summable (fun m : ℕ ↦ Φ.coeff (m + 2) * π[m + 2] X) := by
  -- Shift the already convergent full trace-power series by two degrees.
  let f : ℕ → ℝ := fun k ↦ Φ.coeff k * π[k] X
  have hsum : Summable f := (Φ.matrixFun_hasSum_powerTrace hX).summable
  have htail : Summable (fun m : ℕ ↦ f (m + 2)) := by
    exact (summable_nat_add_iff 2).2 hsum
  simpa [f] using htail
/-- Helper for Theorem 6.10: a centered affine slice through a domain point stays inside
`Φ.dom` on a small interval, while keeping both an ambient Euclidean operator-norm bound and a
crude Frobenius-norm bound. -/
lemma existsCenteredSliceSubsetDomWithOpNormBound
    (Φ : AnalyticSymmetricSpectralFunction) (X : SymmMat) (hX : X ∈ Φ.dom) (H : SymmMat) :
    ∃ ε ρ σ : ℝ, 0 < ε ∧ ρ ∈ Φ.scalarDom ∧
      ∀ {t : ℝ}, t ∈ Set.Ioo (-ε) ε →
        X + t • H ∈ Φ.dom ∧ ‖(((X + t • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + t • H : SymmMat)‖ < σ := by
  obtain ⟨ρ, hXρ, hρdom⟩ := exists_scalarWitness_gt_opNorm_of_mem_dom (Φ := Φ) X hX
  by_cases hHzero : ambientOpNorm (H : Mat) = 0
  · refine ⟨1, ρ, ‖X‖ + ‖H‖ + 1, by positivity, hρdom, ?_⟩
    intro t ht
    have htabs : |t| < 1 := abs_lt_of_mem_centeredInterval ht
    have hsmulMat :
        ‖(((t • H : SymmMat) : Mat))‖ = |t| * ambientOpNorm (H : Mat) := by
      -- On the ambient matrix carrier, scaling contributes exactly a scalar absolute value.
      simpa [ambientOpNorm, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using
        (norm_smul t (H : Mat))
    have hsliceMatLe :
        ‖(((X + t • H : SymmMat) : Mat))‖ ≤
          ambientOpNorm (X : Mat) + |t| * ambientOpNorm (H : Mat) := by
      -- Triangle inequality reduces the slice operator norm to the base point and the scaled direction.
      calc
        ‖(((X + t • H : SymmMat) : Mat))‖ ≤ ‖((X : Mat))‖ + ‖(((t • H : SymmMat) : Mat))‖ := by
            simpa using norm_add_le (X : Mat) (((t • H : SymmMat) : Mat))
        _ = ambientOpNorm (X : Mat) + |t| * ambientOpNorm (H : Mat) := by
            rw [hsmulMat]
            rfl
    have hsliceOp :
        ‖(((X + t • H : SymmMat) : Mat))‖ < ρ := by
      -- If the direction has zero ambient operator norm, the whole slice keeps the original bound.
      have hsum_lt : ambientOpNorm (X : Mat) + |t| * ambientOpNorm (H : Mat) < ρ := by
        nlinarith [hXρ, hHzero]
      exact lt_of_le_of_lt hsliceMatLe hsum_lt
    have hsliceDom : X + t • H ∈ Φ.dom := by
      -- The repaired operator-norm witness feeds directly into the domain-stability bridge.
      exact
        dom_of_opNorm_lt_scalarWitness (Φ := Φ) (Y := X + t • H) hρdom <| by
          simpa [ambientOpNorm] using hsliceOp
    have hsliceNormLe :
        ‖(X + t • H : SymmMat)‖ ≤ ‖X‖ + |t| * ‖H‖ := by
      -- The intrinsic Frobenius norm obeys the same affine-line triangle inequality.
      calc
        ‖(X + t • H : SymmMat)‖ ≤ ‖X‖ + ‖t • H‖ := norm_add_le _ _
        _ = ‖X‖ + |t| * ‖H‖ := by
            simpa [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using (congrArg (fun r : ℝ ↦ ‖X‖ + r) (norm_smul t H))
    have hmulLe : |t| * ‖H‖ ≤ ‖H‖ := by
      simpa using mul_le_mul_of_nonneg_right htabs.le (norm_nonneg H)
    have hsliceNorm :
        ‖(X + t • H : SymmMat)‖ < ‖X‖ + ‖H‖ + 1 := by
      -- A coarse unit-width enlargement is enough for the Frobenius-norm side of the slice package.
      have hsum_lt : ‖X‖ + |t| * ‖H‖ < ‖X‖ + ‖H‖ + 1 := by
        nlinarith
      exact lt_of_le_of_lt hsliceNormLe hsum_lt
    exact ⟨hsliceDom, hsliceOp, hsliceNorm⟩
  · set opX : ℝ := ambientOpNorm (X : Mat)
    set opH : ℝ := ambientOpNorm (H : Mat)
    have hopH_pos : 0 < opH := by
      -- Outside the degenerate branch, the direction has strictly positive ambient operator norm.
      have hopH_nonneg : 0 ≤ opH := by
        simp [opH, ambientOpNorm]
      exact lt_of_le_of_ne hopH_nonneg (by simpa [eq_comm, opH] using hHzero)
    let ε : ℝ := (ρ - opX) / (2 * opH)
    refine ⟨ε, ρ, ‖X‖ + ε * ‖H‖ + 1, ?_, hρdom, ?_⟩
    · -- Choose `ε` from half the operator-norm gap to the scalar-radius witness.
      have hgap_pos : 0 < ρ - opX := by
        simpa [opX] using sub_pos.mpr hXρ
      exact div_pos hgap_pos (by positivity)
    · intro t ht
      have htabs : |t| < ε := abs_lt_of_mem_centeredInterval ht
      have hsmulMat :
          ‖(((t • H : SymmMat) : Mat))‖ = |t| * opH := by
        -- Write the scaled ambient representative in a form where the operator norm is multiplicative.
        simpa [opH, ambientOpNorm, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using
          (norm_smul t (H : Mat))
      have hsliceMatLe :
          ‖(((X + t • H : SymmMat) : Mat))‖ ≤ opX + |t| * opH := by
        -- The affine slice stays close to `X` because both summands are measured in the same norm.
        calc
          ‖(((X + t • H : SymmMat) : Mat))‖ ≤ ‖((X : Mat))‖ + ‖(((t • H : SymmMat) : Mat))‖ := by
              simpa using norm_add_le (X : Mat) (((t • H : SymmMat) : Mat))
          _ = opX + |t| * opH := by
              rw [hsmulMat]
              rfl
      have hεmul : ε * opH = (ρ - opX) / 2 := by
        -- Multiplying the chosen interval radius by `‖H‖` recovers exactly half the original gap.
        calc
          ε * opH = ((ρ - opX) / (2 * opH)) * opH := by rfl
          _ = (ρ - opX) / 2 := by
              field_simp [hopH_pos.ne']
      have hmul_lt : |t| * opH < (ρ - opX) / 2 := by
        -- The centered-interval hypothesis turns into a strict operator-norm increment bound.
        calc
          |t| * opH < ε * opH := by
              exact mul_lt_mul_of_pos_right htabs hopH_pos
          _ = (ρ - opX) / 2 := hεmul
      have hsum_lt : opX + |t| * opH < ρ := by
        nlinarith
      have hsliceOp :
          ‖(((X + t • H : SymmMat) : Mat))‖ < ρ := by
        exact lt_of_le_of_lt hsliceMatLe hsum_lt
      have hsliceDom : X + t • H ∈ Φ.dom := by
        -- Feed the repaired operator-norm control into the domain-stability bridge.
        exact
          dom_of_opNorm_lt_scalarWitness (Φ := Φ) (Y := X + t • H) hρdom <| by
            simpa [ambientOpNorm] using hsliceOp
      have hsliceNormLe :
          ‖(X + t • H : SymmMat)‖ ≤ ‖X‖ + |t| * ‖H‖ := by
        -- The Frobenius norm obeys the same affine-line triangle inequality as above.
        calc
          ‖(X + t • H : SymmMat)‖ ≤ ‖X‖ + ‖t • H‖ := norm_add_le _ _
          _ = ‖X‖ + |t| * ‖H‖ := by
              simpa [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using (congrArg (fun r : ℝ ↦ ‖X‖ + r) (norm_smul t H))
      have hmulLe : |t| * ‖H‖ ≤ ε * ‖H‖ := by
        exact mul_le_mul_of_nonneg_right htabs.le (norm_nonneg H)
      have hsliceNorm :
          ‖(X + t • H : SymmMat)‖ < ‖X‖ + ε * ‖H‖ + 1 := by
        -- The same centered interval gives a coarse intrinsic Frobenius bound on the slice.
        have hsum_lt : ‖X‖ + |t| * ‖H‖ < ‖X‖ + ε * ‖H‖ + 1 := by
          nlinarith
        exact lt_of_le_of_lt hsliceNormLe hsum_lt
      exact ⟨hsliceDom, hsliceOp, hsliceNorm⟩
/-- Helper for Theorem 6.10: the trace of `A Aᵀ` is the sum of the squared entries of `A`. -/
private theorem trace_mul_transpose_eq_sum_squares_local
    (A : Mat) :
    Matrix.trace (A * Matrix.transpose A) = ∑ i : Fin n, ∑ j : Fin n, A i j ^ (2 : ℕ) := by
  -- Rewrite the trace through vectorization, then swap the two finite sums.
  rw [Matrix.trace_mul_comm, ← Matrix.vec_dotProduct_vec A A]
  simp [Matrix.vec, dotProduct, pow_two, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
/-- Helper for Theorem 6.10: the squared Euclidean norm of each column is bounded by the squared
ambient Euclidean operator norm. -/
private theorem columnSqSum_le_l2OperatorNorm_sq_local
    (K : Mat) (i : Fin n) :
    ∑ j : Fin n, (K j i) ^ (2 : ℕ) ≤ ‖K‖ ^ (2 : ℕ) := by
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Pi.single i (1 : ℝ))
  have hxnorm : ‖x‖ = 1 := by
    -- The standard basis vector has Euclidean norm `1`.
    simp [x]
  have hbound :
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm <| Matrix.mulVec K x‖ ≤ ‖K‖ := by
    -- Applying `K` to the `i`th basis vector turns the operator norm bound into a column bound.
    simpa [hxnorm, x] using K.l2_opNorm_mulVec x
  have hsquare :
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm <| Matrix.mulVec K x‖ ^ (2 : ℕ) ≤ ‖K‖ ^ (2 : ℕ) := by
    -- Squaring both sides exposes the column energy.
    simpa [pow_two] using
      (mul_le_mul hbound hbound (norm_nonneg _) (norm_nonneg _))
  have hcolumn_norm :
      ‖WithLp.toLp 2 (K.col i)‖ ^ (2 : ℕ) ≤ ‖K‖ ^ (2 : ℕ) := by
    -- `K *ᵥ e_i` is exactly the `i`th column of `K`.
    simpa [x] using hsquare
  calc
    ∑ j : Fin n, (K j i) ^ (2 : ℕ) = ‖WithLp.toLp 2 (K.col i)‖ ^ (2 : ℕ) := by
      -- Repackage the column-entry sum as the Euclidean norm square of the column.
      symm
      simpa using EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (K.col i))
    _ ≤ ‖K‖ ^ (2 : ℕ) := hcolumn_norm
/-- Helper for Theorem 6.10: the ambient Frobenius norm of a symmetric matrix representative
agrees with the intrinsic `SymmMat` norm. -/
private theorem ambientFrobeniusNorm_coe_eq_symmNorm
    (Y : SymmMat) :
    @norm Mat theoremSixTenAmbientMatrixNormedRing.toNorm (Y : Mat) = ‖Y‖ := by
  -- The inherited `SymmMat` norm is definitionally the ambient Frobenius norm on representatives.
  simpa using (RealSymmetricMatrixSpace.norm_coe Y)
/-- Helper for Theorem 6.10: the ambient Frobenius norm of a square matrix is bounded by
`sqrt n` times its ambient `L²` operator norm. -/
private theorem ambientFrobeniusNorm_le_sqrt_card_mulAmbientOpNorm
    (A : Mat) :
    @norm Mat theoremSixTenAmbientMatrixNormedRing.toNorm A ≤
      Real.sqrt (n : ℝ) * ambientOpNorm A := by
  -- Route correction: instead of pushing the analytic tail estimates first, isolate the finite
  -- dimensional bridge from column energies to the Frobenius/operator comparison here.
  have hsum_le :
      ∑ i : Fin n, ∑ j : Fin n, A j i ^ (2 : ℕ) ≤
        ∑ _i : Fin n, ambientOpNorm A ^ (2 : ℕ) := by
    -- Bound each column energy by the squared ambient operator norm before summing over columns.
    refine Finset.sum_le_sum ?_
    intro i hi
    simpa [ambientOpNorm] using columnSqSum_le_l2OperatorNorm_sq_local (K := A) i
  have hsum_eq :
      (∑ _i : Fin n, ambientOpNorm A ^ (2 : ℕ)) =
        (n : ℝ) * ambientOpNorm A ^ (2 : ℕ) := by
    -- Collapse the constant column bound to `n` copies of the same squared norm.
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hop_nonneg : 0 ≤ ambientOpNorm A := norm_nonneg _
  calc
    @norm Mat theoremSixTenAmbientMatrixNormedRing.toNorm A
      = Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ (2 : ℕ)) := by
          -- Expand the Frobenius owner into the entrywise sum-of-squares formula.
          simpa [Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow] using (Matrix.frobenius_norm_def A)
    _ = Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A j i ^ (2 : ℕ)) := by
          -- Swap the two finite indices so the column estimate applies directly.
          congr 1
          rw [Finset.sum_comm]
    _ ≤ Real.sqrt (∑ _i : Fin n, ambientOpNorm A ^ (2 : ℕ)) := by
          -- Monotonicity of `sqrt` transports the finite column estimate to the Frobenius norm.
          exact Real.sqrt_le_sqrt hsum_le
    _ = Real.sqrt ((n : ℝ) * ambientOpNorm A ^ (2 : ℕ)) := by
          rw [hsum_eq]
    _ = Real.sqrt (n : ℝ) * ambientOpNorm A := by
          -- The remaining square root is exactly `sqrt n * ‖A‖`.
          calc
            Real.sqrt ((n : ℝ) * ambientOpNorm A ^ (2 : ℕ))
                = Real.sqrt (ambientOpNorm A ^ (2 : ℕ)) * Real.sqrt (n : ℝ) := by
                    rw [mul_comm, Real.sqrt_mul (show 0 ≤ ambientOpNorm A ^ (2 : ℕ) by positivity)]
            _ = Real.sqrt (n : ℝ) * ambientOpNorm A := by
                    simp [pow_two, hop_nonneg, mul_comm]
/-- Helper for Theorem 6.10: the Frobenius norm on `𝕊^n` is bounded by `sqrt n` times the ambient
Euclidean operator norm. -/
private theorem frobeniusNorm_le_sqrt_card_mul_opNorm
    (Y : SymmMat) :
    ‖Y‖ ≤ Real.sqrt (n : ℝ) * ‖((Y : Mat))‖ := by
  -- Rewrite the intrinsic norm to the ambient Frobenius owner before applying the matrix bound.
  rw [← ambientFrobeniusNorm_coe_eq_symmNorm]
  -- The right-hand norm is already the local ambient `L²` operator norm.
  simpa [ambientOpNorm] using
    ambientFrobeniusNorm_le_sqrt_card_mulAmbientOpNorm (A := (Y : Mat))
/-- Helper for Theorem 6.10: a symmetric matrix whose ambient `L²` operator norm is bounded by
`ρ` has every Frobenius power `Y ^ m` bounded by `sqrt n * ρ^m`. This is the stable bridge from
the centered slice's operator-norm control to the Frobenius estimates needed for the
first-derivative slice family. -/
private theorem frobeniusNorm_pow_le_sqrt_card_mul_opNormPow
    (Y : SymmMat) (m : ℕ) {ρ : ℝ} (hρ : ‖((Y : Mat))‖ < ρ) :
    ‖Y ^ m‖ ≤ Real.sqrt (n : ℝ) * ρ ^ m := by
  have hpowNorm :
      ‖((((Y ^ m : SymmMat) : Mat)))‖ ≤ ‖((Y : Mat))‖ ^ m := by
    -- Coercing the symmetric power to ambient matrices gives the same matrix power.
    cases m with
    | zero =>
        simpa [ambientOpNorm] using (ambientOpNorm_one_le_one (n := n))
    | succ m =>
        simpa using (norm_pow_le' (a := (Y : Mat)) (n := m + 1) (Nat.succ_pos _))
  have hρpow : ‖((Y : Mat))‖ ^ m ≤ ρ ^ m := by
    -- The strict operator-norm bound propagates monotonically through natural powers.
    exact pow_le_pow_left₀ (by simpa using norm_nonneg ((Y : Mat))) hρ.le m
  calc
    ‖Y ^ m‖ ≤ Real.sqrt (n : ℝ) * ‖((((Y ^ m : SymmMat) : Mat)))‖ := by
      -- First compare the Frobenius norm of `Y ^ m` with its ambient operator norm.
      exact frobeniusNorm_le_sqrt_card_mul_opNorm (Y := Y ^ m)
    _ ≤ Real.sqrt (n : ℝ) * ‖((Y : Mat))‖ ^ m := by
      -- Then replace the ambient operator norm of the power by the powered operator norm.
      exact mul_le_mul_of_nonneg_left hpowNorm (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (n : ℝ) * ρ ^ m := by
      -- Finally use the scalar witness `ρ` dominating the base operator norm.
      exact mul_le_mul_of_nonneg_left hρpow (Real.sqrt_nonneg _)
/-- Helper for Theorem 6.10: the ambient Frobenius norm of the ambient representative of `Y ^ m`
obeys the same operator-norm power bound as the intrinsic `SymmMat` norm. -/
private theorem ambientFrobeniusNorm_pow_le_sqrt_card_mul_opNormPow
    (Y : SymmMat) (m : ℕ) {ρ : ℝ} (hρ : ‖((Y : Mat))‖ < ρ) :
    @norm Mat theoremSixTenAmbientMatrixNormedRing.toNorm (((Y ^ m : SymmMat) : Mat)) ≤
      Real.sqrt (n : ℝ) * ρ ^ m := by
  -- Rewrite the ambient Frobenius owner of `Y ^ m` back to the intrinsic symmetric norm.
  rw [ambientFrobeniusNorm_coe_eq_symmNorm]
  -- The intrinsic Frobenius bound was established in the previous helper.
  exact frobeniusNorm_pow_le_sqrt_card_mul_opNormPow (Y := Y) (m := m) hρ
/-- Helper for Theorem 6.10: at interior points of the centered interval, the first within-derivative
of a coefficient slice is the translated Proposition 6.33 Frobenius pairing. -/
private lemma coeffMulPowerTraceSlice_iteratedDerivWithin_one_eq_frobenius
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat)
    {ε : ℝ} {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) :
    iteratedDerivWithin 1
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        (Set.Ioo (-ε) ε) t =
      Φ.coeff k * ((k : ℝ) * ⟪(X + t • H) ^ (k - 1), H⟫_F) := by
  have hcontAt :
      ContDiffAt ℝ 1
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        t := by
    -- The coefficient slice is smooth on the whole line, so the within-derivative agrees with the
    -- ordinary derivative at interior points of the centered interval.
    have hbase :
        ContDiff ℝ 1 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) := by
      exact (coeff_mul_powerTrace_contDiff (Φ := Φ) k).of_le
        (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
    have hline : ContDiff ℝ 1 (fun s : ℝ ↦ X + s • H) := by
      -- The translated slice is affine in the scalar parameter.
      fun_prop
    simpa [Function.comp] using (hbase.comp hline).contDiffAt
  have hwithin :
      iteratedDerivWithin 1
          (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
          (Set.Ioo (-ε) ε) t =
        iteratedDeriv 1
          (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
          t := by
    -- Interior points of the open interval may be handled with the ordinary first derivative.
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Ioo (-ε : ℝ) ε)
        hcontAt
        ht
  have hpowerDeriv :
      HasDerivAt
        (fun s : ℝ ↦ π[k] (X + s • H))
        ((k : ℝ) * ⟪(X + t • H) ^ (k - 1), H⟫_F)
        t := by
    have hk1 : 1 ≤ k := by omega
    have hdiffAt :
        DifferentiableAt ℝ (π[k] : SymmMat → ℝ) (X + t • H) := by
      -- Proposition 6.33 already puts `π[k]` on the `C²` surface needed for the chain rule.
      exact
        ((powerTrace_contDiff_local (k := k) hk1).contDiffAt).differentiableAt
    have hcomp :
        HasDerivAt
          (fun s : ℝ ↦ π[k] (X + s • H))
          ((fderiv ℝ (π[k] : SymmMat → ℝ) (X + t • H)) H)
          t := by
      -- Differentiate the affine slice first, then insert the direction `H` into the Fréchet derivative.
      exact hdiffAt.hasFDerivAt.comp_hasDerivAt t (affineLineHasDerivAt X H t)
    -- Proposition 6.33 identifies the Fréchet derivative of `π[k]` with the Frobenius pairing.
    simpa [powerTrace_fderiv_eq_frobenius (n := n) k (by omega) (X + t • H) H] using hcomp
  have hscaled :
      HasDerivAt
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        (Φ.coeff k * ((k : ℝ) * ⟪(X + t • H) ^ (k - 1), H⟫_F))
        t := by
    -- The coefficient `Φ.coeff k` is constant along the slice, so it pulls through the derivative.
    simpa [mul_assoc] using hpowerDeriv.const_mul (Φ.coeff k)
  calc
    iteratedDerivWithin 1
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        (Set.Ioo (-ε) ε) t
      =
        iteratedDeriv 1
          (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
          t := hwithin
    _ = deriv (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H)) t := by
          simp [iteratedDeriv_one]
    _ = Φ.coeff k * ((k : ℝ) * ⟪(X + t • H) ^ (k - 1), H⟫_F) := hscaled.deriv

/-- Helper for Theorem 6.10: once the centered slice keeps `X + t • H` below the operator-norm
radius witness `ρ`, every higher-degree (`k ≥ 2`) coefficient slice has a first derivative bounded
by the shifted scalar majorant used in the termwise differentiation step. -/
private theorem norm_iteratedDerivWithin_one_coeffSlice_le
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat)
    {ε ρ σ t : ℝ} {k : ℕ} (hk : 2 ≤ k) (ht : t ∈ Set.Ioo (-ε) ε)
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    ‖iteratedDerivWithin 1 (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H)) (Set.Ioo (-ε) ε) t‖ ≤
      Real.sqrt (n : ℝ) * ‖H‖ * (Φ.coeff k * (((k : ℕ) : ℝ) * ρ ^ (k - 1))) := by
  obtain ⟨_, hXtOp, _⟩ := hsliceOp (u := t) ht
  have hρpos : 0 < ρ := lt_of_le_of_lt (by simpa [ambientOpNorm] using norm_nonneg ((X + t • H : SymmMat) : Mat)) hXtOp
  have hcoeff_nonneg : 0 ≤ Φ.coeff k := Φ.coeff_nonneg k hk
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hinner :
      ‖⟪(X + t • H) ^ (k - 1), H⟫_F‖ ≤ ‖(X + t • H) ^ (k - 1)‖ * ‖H‖ := by
    -- Cauchy-Schwarz bounds the Frobenius pairing by the product of the Frobenius norms.
    simpa using norm_inner_le_norm (𝕜 := ℝ) ((X + t • H) ^ (k - 1)) H
  have hpow :
      ‖(X + t • H) ^ (k - 1)‖ ≤ Real.sqrt (n : ℝ) * ρ ^ (k - 1) :=
    frobeniusNorm_pow_le_sqrt_card_mul_opNormPow
      (Y := X + t • H) (m := k - 1) hXtOp
  calc
    ‖iteratedDerivWithin 1
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        (Set.Ioo (-ε) ε) t‖
      =
        ‖Φ.coeff k * ((k : ℝ) * ⟪(X + t • H) ^ (k - 1), H⟫_F)‖ := by
            rw [coeffMulPowerTraceSlice_iteratedDerivWithin_one_eq_frobenius
              (Φ := Φ) (X := X) (H := H) hk ht]
    _ = Φ.coeff k * ((k : ℝ) * ‖⟪(X + t • H) ^ (k - 1), H⟫_F‖) := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg hcoeff_nonneg, Real.norm_of_nonneg hk_nonneg]
    _ ≤ Φ.coeff k * ((k : ℝ) * (‖(X + t • H) ^ (k - 1)‖ * ‖H‖)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hk_nonneg) hcoeff_nonneg
    _ ≤ Φ.coeff k * ((k : ℝ) * ((Real.sqrt (n : ℝ) * ρ ^ (k - 1)) * ‖H‖)) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hpow (norm_nonneg H))
                hk_nonneg)
              hcoeff_nonneg
    _ = Real.sqrt (n : ℝ) * ‖H‖ * (Φ.coeff k * (((k : ℕ) : ℝ) * ρ ^ (k - 1))) := by
          ring
end L2OperatorSlice

/-- Helper for Theorem 6.10: coefficient-scaled trace-power slices are smooth of all orders, so
every `iteratedDerivWithin k` used in the shifted-tail differentiation argument is differentiable
at interior points of the centered interval. -/
private theorem coeff_mul_powerTrace_contDiff_all
    (Φ : AnalyticSymmetricSpectralFunction) (k : ℕ) :
    ContDiff ℝ ⊤ (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) := by
  have hambientPow : ContDiff ℝ ⊤ (fun A : Mat ↦ A ^ k) := by
    -- Matrix powers are polynomial, so they are smooth of all orders.
    fun_prop
  have hambientTrace : ContDiff ℝ ⊤ (fun A : Mat ↦ Matrix.trace (A ^ k)) := by
    -- Evaluate the ambient power through the packaged trace map so `fun_prop` sees a linear map.
    simpa [Function.comp, theoremSixTenTraceContinuousLinearMap_apply] using
      (theoremSixTenTraceContinuousLinearMap (n := n)).contDiff.comp hambientPow
  have hpowerTrace : ContDiff ℝ ⊤ (π[k] : SymmMat → ℝ) := by
    -- Restrict the ambient trace-power owner back to `SymmMat` along the bundled inclusion.
    simpa [RealSymmetricMatrixSpace.powerTrace_def, Function.comp,
      theoremSixTenSymmetricInclusion_apply] using
      hambientTrace.comp (theoremSixTenSymmetricInclusion (n := n)).contDiff
  simpa [smul_eq_mul] using hpowerTrace.const_smul (Φ.coeff k)
/-- Helper for Theorem 6.10: fixing `X`, `H`, and `k`, the coefficient-scaled trace-power slice
`t ↦ Φ.coeff k * π[k] (X + t • H)` is smooth of all orders on `ℝ`. -/
private lemma coeffMulPowerTraceSlice_contDiffAll
    (Φ : AnalyticSymmetricSpectralFunction)
    (k : ℕ) (X H : SymmMat) :
    ContDiff ℝ ⊤ (fun t : ℝ ↦ Φ.coeff k * π[k] (X + t • H)) := by
  have hline : ContDiff ℝ ⊤ (fun t : ℝ ↦ X + t • H) := by
    -- The scalar slice is affine in `t`.
    fun_prop
  simpa [Function.comp] using
    (coeff_mul_powerTrace_contDiff_all (Φ := Φ) (k := k)).comp hline
/-- Helper for Theorem 6.10: each shifted coefficient slice has differentiable `k`th
`iteratedDerivWithin` at interior points of the centered interval, which is the `hf2` input for
`iteratedDerivWithin_tsum`. -/
lemma differentiableAt_iteratedDerivWithin_coeffSlice
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε : ℝ}
    (m a : ℕ) {r : ℝ} (_ha : a ≤ 2) (hr : r ∈ Set.Ioo (-ε) ε) :
    DifferentiableAt ℝ
      (iteratedDerivWithin a
        (fun t : ℝ ↦ Φ.coeff m * π[m] (X + t • H))
        (Set.Ioo (-ε) ε))
      r := by
  have hcontOn :
      ContDiffOn ℝ ⊤
        (fun t : ℝ ↦ Φ.coeff m * π[m] (X + t • H))
        (Set.Ioo (-ε) ε) :=
    (coeffMulPowerTraceSlice_contDiffAll (Φ := Φ) (k := m) X H).contDiffOn
  have hdiffWithin :
      DifferentiableWithinAt ℝ
        (iteratedDerivWithin a
          (fun t : ℝ ↦ Φ.coeff m * π[m] (X + t • H))
          (Set.Ioo (-ε) ε))
        (Set.Ioo (-ε) ε)
        r := by
    -- On the open interval, smooth coefficient slices have differentiable iterated derivatives.
    exact
      hcontOn r hr |>.differentiableWithinAt_iteratedDerivWithin
        (by simp)
        (by simpa [Set.insert_eq_of_mem hr] using uniqueDiffOn_Ioo (-ε : ℝ) ε)
  -- Interior differentiability on the open interval upgrades to ordinary differentiability.
  exact hdiffWithin.differentiableAt (isOpen_Ioo.mem_nhds hr)

/-- Helper for Theorem 6.10: the shifted tail is the degree-`≥ 2` specialization of the general
coefficient-slice differentiability bridge. -/
lemma differentiableAt_iteratedDerivWithin_coeffSliceTail
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε : ℝ}
    (m a : ℕ) {r : ℝ} (_ha : a ≤ 2) (hr : r ∈ Set.Ioo (-ε) ε) :
    DifferentiableAt ℝ
      (iteratedDerivWithin a
        (fun t : ℝ ↦ Φ.coeff (m + 2) * π[m + 2] (X + t • H))
        (Set.Ioo (-ε) ε))
      r := by
  -- Reindex the general coefficient family to the shifted tail.
  simpa using
    differentiableAt_iteratedDerivWithin_coeffSlice
      (Φ := Φ) (X := X) (H := H) (ε := ε) (m := m + 2) (a := a) (r := r) _ha hr
/-- Helper for Theorem 6.10: the shifted-tail first-derivative family is summable locally
uniformly on the centered interval, using the existing higher-degree derivative bound and the
shifted scalar majorant series. -/
lemma summableLocallyUniformlyOn_iteratedDerivWithin_one_coeffSliceTail
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ σ : ℝ}
    (hρ : ρ ∈ Φ.scalarDom)
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    SummableLocallyUniformlyOn
      (fun m : ℕ ↦
        iteratedDerivWithin 1
          (fun t : ℝ ↦ Φ.coeff (m + 2) * π[m + 2] (X + t • H))
          (Set.Ioo (-ε) ε))
      (Set.Ioo (-ε) ε) := by
  let u : ℕ → ℝ := fun m ↦
    Real.sqrt (n : ℝ) * ‖H‖ *
      (Φ.coeff (m + 2) * (((m + 2 : ℕ) : ℝ) * ρ ^ (m + 1)))
  -- Package the global first-derivative majorant as a locally uniform bound on the centered interval.
  refine SummableLocallyUniformlyOn_of_locally_bounded isOpen_Ioo ?_
  intro K hK hKcompact
  refine ⟨u, ?_, ?_⟩
  · -- The majorant is a fixed scalar multiple of the shifted first-derivative coefficient series.
    simpa only [u, mul_assoc, mul_left_comm, mul_comm] using
      (scalarFirstDerivSeries_summable_shifted (Φ := Φ) hρ).mul_left
        (Real.sqrt (n : ℝ) * ‖H‖)
  · intro m t ht
    have ht' : t ∈ Set.Ioo (-ε) ε := hK ht
    -- Apply the pointwise first-derivative estimate at the translated slice point `t`.
    simpa only [u, Nat.add_assoc, mul_assoc, mul_left_comm, mul_comm] using
      norm_iteratedDerivWithin_one_coeffSlice_le
        (Φ := Φ) (X := X) (H := H)
        (ε := ε) (ρ := ρ) (σ := σ)
        (t := t) (k := m + 2)
        (by omega) ht' hsliceOp
/-- Helper for Theorem 6.10: on the centered open interval, the second within-derivative of a
coefficient slice equals the ambient Hessian quadratic form at the translated base point. -/
private lemma iteratedDerivWithin_two_coeffSlice_eq_hessianAt
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε : ℝ} {k : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (-ε) ε) :
    iteratedDerivWithin 2
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        (Set.Ioo (-ε) ε) t =
      (iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) (X + t • H)) ![H, H] := by
  let f : SymmMat → ℝ := fun Y : SymmMat ↦ Φ.coeff k * π[k] Y
  let g : ℝ → ℝ := fun s : ℝ ↦ f (X + s • H)
  have hcontWithin :
      ContDiffAt ℝ 2 g t := by
    -- The coefficient slice is globally smooth, so its within-second derivative agrees with the
    -- ordinary second derivative at interior points of the open interval.
    simpa [f, g] using
      ((coeffMulPowerTraceSlice_contDiffAll (Φ := Φ) (k := k) X H).of_le
        (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)).contDiffAt
  have hwithin :
      iteratedDerivWithin 2 g (Set.Ioo (-ε) ε) t = iteratedDeriv 2 g t := by
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Ioo (-ε : ℝ) ε)
        hcontWithin
        ht
  have hshift :
      iteratedDeriv 2 g t =
        iteratedDeriv 2 (fun s : ℝ ↦ f ((X + t • H) + s • H)) 0 := by
    -- Shift the affine slice so the generic `slice_secondDeriv_eq_iteratedFDeriv_two` lemma can
    -- be applied at the translated base point `X + t • H`.
    have hcomp :=
      congrArg (fun h : ℝ → ℝ ↦ h 0)
        (iteratedDeriv_comp_const_add (n := 2) (f := g) (s := t))
    simpa [f, g, add_assoc, add_left_comm, add_comm, add_smul] using hcomp.symm
  have hslice :
      iteratedDeriv 2 (fun s : ℝ ↦ f ((X + t • H) + s • H)) 0 =
        (iteratedFDeriv ℝ 2 f (X + t • H)) ![H, H] := by
    -- Now the existing slice-to-Hessian bridge applies at the translated base point.
    exact
      slice_secondDeriv_eq_iteratedFDeriv_two
        (X := X + t • H)
        (H := H)
        (((coeff_mul_powerTrace_contDiff_all (Φ := Φ) (k := k)).of_le
          (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)).contDiffAt)
  calc
    iteratedDerivWithin 2
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        (Set.Ioo (-ε) ε) t
      = iteratedDeriv 2 g t := by
          change iteratedDerivWithin 2 g (Set.Ioo (-ε) ε) t = iteratedDeriv 2 g t
          exact hwithin
    _ = iteratedDeriv 2 (fun s : ℝ ↦ f ((X + t • H) + s • H)) 0 := hshift
    _ = (iteratedFDeriv ℝ 2 f (X + t • H)) ![H, H] := hslice
    _ =
        (iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) (X + t • H)) ![H, H] := by
          simp [f]
/-- Helper for Theorem 6.10: at interior points of the centered interval, the second
within-derivative of a coefficient slice is exactly the translated Proposition 6.33 Frobenius
sum. -/
private lemma coeffMulPowerTraceSlice_iteratedDerivWithin_two_eq_frobeniusSum
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat)
    {ε : ℝ} {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) :
    iteratedDerivWithin 2
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        (Set.Ioo (-ε) ε) t =
      Φ.coeff k *
        ((k : ℝ) *
          (Finset.range (k - 1)).sum fun p ↦ sandwichTraceTerm k p (X + t • H) H) := by
  have hpowerCont :
      ContDiffAt ℝ 2 (π[k] : SymmMat → ℝ) (X + t • H) := by
    -- Proposition 6.33 already provides `C²` regularity of `π[k]` at the translated base point.
    simpa using ((powerTrace_contDiff_local (k := k) (by omega)).contDiffAt : ContDiffAt ℝ 2 (π[k] : SymmMat → ℝ) (X + t • H))
  have hiter :
      (iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) (X + t • H)) ![H, H] =
        Φ.coeff k * ((iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) (X + t • H)) ![H, H]) := by
    -- Pull the scalar coefficient through the repeated Fréchet derivative before using the
    -- Proposition 6.33 normal form.
    have hsmul :
        iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k • π[k] Y) (X + t • H) =
          Φ.coeff k • iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) (X + t • H) :=
      iteratedFDeriv_const_smul_apply' hpowerCont
    simpa [Pi.smul_apply, smul_eq_mul] using congrArg (fun T ↦ T ![H, H]) hsmul
  calc
    iteratedDerivWithin 2
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        (Set.Ioo (-ε) ε) t
      =
        (iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) (X + t • H)) ![H, H] :=
          iteratedDerivWithin_two_coeffSlice_eq_hessianAt (Φ := Φ) (X := X) (H := H) ht
    _ = Φ.coeff k * ((iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) (X + t • H)) ![H, H]) := hiter
    _ =
        Φ.coeff k *
          ((k : ℝ) *
            (Finset.range (k - 1)).sum fun p ↦ sandwichTraceTerm k p (X + t • H) H) := by
          rw [powerTrace_iteratedFDeriv_two_eq_frobenius_sum (n := n) (k := k) (by omega) (X + t • H) H]
/-- Helper for Theorem 6.10: each translated Proposition 6.33 sandwich trace term is controlled
by the centered slice's operator-norm witness and the ambient Frobenius/operator bridge. -/
private lemma sandwichTraceTerm_norm_le_shiftedOpNormMajorant
    (Y H : SymmMat) {ρ : ℝ} {k p : ℕ}
    (hY : ‖((Y : Mat))‖ < ρ) (hp : p ∈ Finset.range (k - 1)) :
    ‖sandwichTraceTerm k p Y H‖ ≤
      (theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ) *
        ρ ^ (k - 2) := by
  have hρ_nonneg : 0 ≤ ρ := le_trans (by simpa [ambientOpNorm] using norm_nonneg (Y : Mat)) hY.le
  have hp_le : p ≤ k - 2 := by
    have hkm1 : k - 1 = (k - 2) + 1 := by omega
    rw [hkm1] at hp
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  have hpow_split : ρ ^ p * ρ ^ (k - 2 - p) = ρ ^ (k - 2) := by
    simpa [Nat.add_sub_of_le hp_le] using (pow_add ρ p (k - 2 - p)).symm
  have htranspose :
      ‖((((((Y ^ p : SymmMat) : Mat) * (H : Mat) *
          (((Y ^ (k - 2 - p) : SymmMat) : Mat))).transpose))‖ =
        ‖(((Y ^ p : SymmMat) : Mat) * (H : Mat) *
          (((Y ^ (k - 2 - p) : SymmMat) : Mat))‖ := by
    -- Frobenius norm is invariant under transpose on ambient matrices.
    simpa [theoremSixTenAmbientMatrixNormedRing] using
      (Matrix.frobenius_norm_transpose
        ((((Y ^ p : SymmMat) : Mat) * (H : Mat) *
          (((Y ^ (k - 2 - p) : SymmMat) : Mat))))
  have hpowp :
      ‖(((Y ^ p : SymmMat) : Mat))‖ ≤ Real.sqrt (n : ℝ) * ρ ^ p :=
    ambientFrobeniusNorm_pow_le_sqrt_card_mul_opNormPow (Y := Y) (m := p) hY
  have hpowkp :
      ‖(((Y ^ (k - 2 - p) : SymmMat) : Mat))‖ ≤ Real.sqrt (n : ℝ) * ρ ^ (k - 2 - p) :=
    ambientFrobeniusNorm_pow_le_sqrt_card_mul_opNormPow (Y := Y) (m := k - 2 - p) hY
  have hsqrt :
      Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith [Real.sq_sqrt hn]
  calc
    ‖sandwichTraceTerm k p Y H‖
      ≤ (theoremSixTenTraceContinuousLinearMapNorm (n := n)) *
          ‖((((((Y ^ p : SymmMat) : Mat) * (H : Mat) *
              (((Y ^ (k - 2 - p) : SymmMat) : Mat))).transpose) * (H : Mat))‖ := by
            simpa [sandwichTraceTerm, theoremSixTenTraceContinuousLinearMap_apply] using
              (ContinuousLinearMap.le_opNorm
                (theoremSixTenTraceContinuousLinearMap (n := n))
                ((((((Y ^ p : SymmMat) : Mat) * (H : Mat) *
                    (((Y ^ (k - 2 - p) : SymmMat) : Mat))).transpose) * (H : Mat))))
    _ ≤ (theoremSixTenTraceContinuousLinearMapNorm (n := n)) *
          (‖((((Y ^ p : SymmMat) : Mat) * (H : Mat) *
              (((Y ^ (k - 2 - p) : SymmMat) : Mat))).transpose)‖ * ‖(H : Mat)‖) := by
            gcongr
            exact norm_mul_le _ _
    _ = (theoremSixTenTraceContinuousLinearMapNorm (n := n)) *
          (‖(((Y ^ p : SymmMat) : Mat) * (H : Mat) *
              (((Y ^ (k - 2 - p) : SymmMat) : Mat))‖ * ‖(H : Mat)‖) := by
            rw [htranspose]
    _ ≤ (theoremSixTenTraceContinuousLinearMapNorm (n := n)) *
          (((‖(((Y ^ p : SymmMat) : Mat))‖ * ‖(H : Mat)‖) *
              ‖(((Y ^ (k - 2 - p) : SymmMat) : Mat))‖) * ‖(H : Mat)‖) := by
            gcongr
            calc
              ‖(((Y ^ p : SymmMat) : Mat) * (H : Mat) *
                  (((Y ^ (k - 2 - p) : SymmMat) : Mat))‖
                ≤ ‖(((Y ^ p : SymmMat) : Mat) * (H : Mat))‖ *
                    ‖(((Y ^ (k - 2 - p) : SymmMat) : Mat))‖ := norm_mul_le _ _
              _ ≤ (‖(((Y ^ p : SymmMat) : Mat))‖ * ‖(H : Mat)‖) *
                    ‖(((Y ^ (k - 2 - p) : SymmMat) : Mat))‖ := by
                      gcongr
                      exact norm_mul_le _ _
    _ ≤ (theoremSixTenTraceContinuousLinearMapNorm (n := n)) *
          ((((Real.sqrt (n : ℝ) * ρ ^ p) * ‖H‖) *
              (Real.sqrt (n : ℝ) * ρ ^ (k - 2 - p))) * ‖H‖) := by
            have hH :
                ‖(H : Mat)‖ = ‖H‖ :=
              ambientFrobeniusNorm_coe_eq_symmNorm H
            rw [hH, hH]
            gcongr
    _ = (theoremSixTenTraceContinuousLinearMapNorm (n := n)) *
          (((Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) *
              ‖H‖ ^ (2 : ℕ)) * (ρ ^ p * ρ ^ (k - 2 - p))) := by
            ring
    _ = (theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ) *
          ρ ^ (k - 2) := by
            rw [hsqrt, hpow_split]
            ring
/-- Helper for Theorem 6.10: on the centered interval where the affine slice stays below the
operator-norm radius `ρ`, every higher-degree coefficient slice has a second derivative bounded by
a fixed trace/Frobenius constant times the shifted scalar majorant series. -/
private theorem norm_iteratedDerivWithin_two_coeffSlice_le
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat)
    {ε ρ σ t : ℝ} {k : ℕ} (hk : 2 ≤ k) (ht : t ∈ Set.Ioo (-ε) ε)
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    ‖iteratedDerivWithin 2
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        (Set.Ioo (-ε) ε) t‖ ≤
      ((theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ)) *
        (Φ.coeff k * ((((k * (k - 1) : ℕ) : ℝ) * ρ ^ (k - 2)))) := by
  obtain ⟨_, hXtOp, _⟩ := hsliceOp (u := t) ht
  have hcoeff_nonneg : 0 ≤ Φ.coeff k := Φ.coeff_nonneg k hk
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hsum_bound :
      ‖(Finset.range (k - 1)).sum fun p ↦
          sandwichTraceTerm k p (X + t • H) H‖ ≤
        (k - 1 : ℝ) *
          ((theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ) *
            ρ ^ (k - 2)) := by
    calc
      ‖(Finset.range (k - 1)).sum fun p ↦
          sandwichTraceTerm k p (X + t • H) H‖
        ≤ Finset.sum (Finset.range (k - 1)) fun p ↦
            ‖sandwichTraceTerm k p (X + t • H) H‖ := by
              exact norm_sum_le _ _
      _ ≤ Finset.sum (Finset.range (k - 1)) fun _ : ℕ ↦
            (theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ) *
              ρ ^ (k - 2) := by
            refine Finset.sum_le_sum ?_
            intro p hp
            exact sandwichTraceTerm_norm_le_shiftedOpNormMajorant
              (Y := X + t • H) (H := H) (k := k) (p := p) hXtOp hp
      _ = (k - 1 : ℝ) *
            ((theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ) *
              ρ ^ (k - 2)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc
    ‖iteratedDerivWithin 2
        (fun s : ℝ ↦ Φ.coeff k * π[k] (X + s • H))
        (Set.Ioo (-ε) ε) t‖
      =
        ‖Φ.coeff k *
          ((k : ℝ) *
            (Finset.range (k - 1)).sum fun p ↦ sandwichTraceTerm k p (X + t • H) H)‖ := by
            rw [coeffMulPowerTraceSlice_iteratedDerivWithin_two_eq_frobeniusSum
              (Φ := Φ) (X := X) (H := H) hk ht]
    _ =
        Φ.coeff k *
          ((k : ℝ) *
            ‖(Finset.range (k - 1)).sum fun p ↦
                sandwichTraceTerm k p (X + t • H) H‖) := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg hcoeff_nonneg, Real.norm_of_nonneg hk_nonneg]
    _ ≤
        Φ.coeff k *
          ((k : ℝ) *
            ((k - 1 : ℝ) *
              ((theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ) *
                ρ ^ (k - 2)))) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsum_bound hk_nonneg)
              hcoeff_nonneg
    _ =
        ((theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ)) *
          (Φ.coeff k * ((((k * (k - 1) : ℕ) : ℝ) * ρ ^ (k - 2)))) := by
            norm_num
            ring
/-- Helper for Theorem 6.10: once the centered slice stays below the operator-norm radius `ρ`,
the shifted-tail second-derivative family has a summable locally uniform majorant obtained from
the exact Proposition 6.33 mixed-trace formula and Frobenius submultiplicativity. -/
lemma summableLocallyUniformlyOn_iteratedDerivWithin_two_coeffSliceTail
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ σ : ℝ}
    (hρ : ρ ∈ Φ.scalarDom)
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    SummableLocallyUniformlyOn
      (fun m : ℕ ↦
        iteratedDerivWithin 2
          (fun t : ℝ ↦ Φ.coeff (m + 2) * π[m + 2] (X + t • H))
          (Set.Ioo (-ε) ε))
      (Set.Ioo (-ε) ε) := by
  let u : ℕ → ℝ := fun m ↦
    ((theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ)) *
      (Φ.coeff (m + 2) * (((((m + 2) * (m + 1) : ℕ) : ℝ) * ρ ^ m)))
  refine SummableLocallyUniformlyOn_of_locally_bounded isOpen_Ioo ?_
  intro K hK hKcompact
  refine ⟨u, ?_, ?_⟩
  · -- The majorant is a fixed scalar multiple of the shifted scalar second-derivative series.
    have hscalar :
        Summable
          (fun m : ℕ ↦
            Φ.coeff (m + 2) * (((((m + 2) * (m + 1) : ℕ) : ℝ) * ρ ^ m))) := by
      have hbase := (scalarSecondDerivSeries_hasSum_shifted (Φ := Φ) hρ).summable
      have hshift : Function.Injective (fun m : ℕ ↦ m + 2) := by
        intro a b hab
        exact Nat.succ.inj <| Nat.succ.inj hab
      simpa [Nat.add_assoc, mul_assoc, mul_left_comm, mul_comm] using hbase.comp_injective hshift
    simpa only [u, mul_assoc, mul_left_comm, mul_comm] using
      hscalar.mul_left
        ((theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ))
  · intro m t ht
    have ht' : t ∈ Set.Ioo (-ε) ε := hK ht
    -- Apply the pointwise second-derivative majorant at the translated slice point `t`.
    simpa only [u, Nat.add_assoc, mul_assoc, mul_left_comm, mul_comm] using
      norm_iteratedDerivWithin_two_coeffSlice_le
        (Φ := Φ) (X := X) (H := H)
        (ε := ε) (ρ := ρ) (σ := σ)
        (t := t) (k := m + 2)
        (by omega) ht' hsliceOp

/-- Helper for Theorem 6.10: the full first-derivative coefficient-slice family is summable
locally uniformly on the centered interval because the degree-`0/1` head is cofinite noise and
the degree-`≥ 2` tail already has a summable locally uniform majorant. -/
private lemma summableLocallyUniformlyOn_iteratedDerivWithin_one_coeffSlice
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ σ : ℝ}
    (hρ : ρ ∈ Φ.scalarDom)
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    SummableLocallyUniformlyOn
      (fun k : ℕ ↦
        iteratedDerivWithin 1
          (fun t : ℝ ↦ Φ.coeff k * π[k] (X + t • H))
          (Set.Ioo (-ε) ε))
      (Set.Ioo (-ε) ε) := by
  let u : ℕ → ℝ := fun k ↦
    if hk : 2 ≤ k then
      Real.sqrt (n : ℝ) * ‖H‖ * (Φ.coeff k * (((k : ℕ) : ℝ) * ρ ^ (k - 1)))
    else 0
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually isOpen_Ioo
  intro K hK hKcompact
  refine ⟨u, ?_, ?_⟩
  · have htail :
        Summable
          (fun m : ℕ ↦
            Real.sqrt (n : ℝ) * ‖H‖ *
              (Φ.coeff (m + 2) * (((m + 2 : ℕ) : ℝ) * ρ ^ (m + 1))) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (scalarFirstDerivSeries_summable_shifted (Φ := Φ) hρ).mul_left
          (Real.sqrt (n : ℝ) * ‖H‖)
    have huTail : Summable (fun m : ℕ ↦ u (m + 2)) := by
      simpa [u, Nat.add_assoc, if_pos (by omega)] using htail
    exact (summable_nat_add_iff 2).1 huTail
  · have hcof : ∀ᶠ k : ℕ in cofinite, 2 ≤ k := by
      refine Filter.mem_cofinite.mpr ?_
      simpa [Nat.not_le, Finset.mem_range] using
        (Finset.finite_toSet (Finset.range 2))
    filter_upwards [hcof] with k hk t ht
    have ht' : t ∈ Set.Ioo (-ε) ε := hK ht
    -- Once the finite head is discarded, the existing tail estimate controls the full family.
    simpa [u, hk] using
      norm_iteratedDerivWithin_one_coeffSlice_le
        (Φ := Φ) (X := X) (H := H)
        (ε := ε) (ρ := ρ) (σ := σ)
        (t := t) (k := k)
        hk ht' hsliceOp

/-- Helper for Theorem 6.10: the full second-derivative coefficient-slice family is summable
locally uniformly on the centered interval for the same cofinite tail reason. -/
private lemma summableLocallyUniformlyOn_iteratedDerivWithin_two_coeffSlice
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ σ : ℝ}
    (hρ : ρ ∈ Φ.scalarDom)
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    SummableLocallyUniformlyOn
      (fun k : ℕ ↦
        iteratedDerivWithin 2
          (fun t : ℝ ↦ Φ.coeff k * π[k] (X + t • H))
          (Set.Ioo (-ε) ε))
      (Set.Ioo (-ε) ε) := by
  let u : ℕ → ℝ := fun k ↦
    if hk : 2 ≤ k then
      ((theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ)) *
        (Φ.coeff k * ((((k * (k - 1) : ℕ) : ℝ) * ρ ^ (k - 2))))
    else 0
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually isOpen_Ioo
  intro K hK hKcompact
  refine ⟨u, ?_, ?_⟩
  · have htail :
        Summable
          (fun m : ℕ ↦
            ((theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ)) *
              (Φ.coeff (m + 2) * (((((m + 2) * (m + 1) : ℕ) : ℝ) * ρ ^ m))) := by
      have hscalar :
          Summable
            (fun m : ℕ ↦
              Φ.coeff (m + 2) * (((((m + 2) * (m + 1) : ℕ) : ℝ) * ρ ^ m))) :=
        (scalarSecondDerivSeries_hasSum_shifted (Φ := Φ) hρ).summable
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        hscalar.mul_left
          ((theoremSixTenTraceContinuousLinearMapNorm (n := n)) * (n : ℝ) * ‖H‖ ^ (2 : ℕ))
    have huTail : Summable (fun m : ℕ ↦ u (m + 2)) := by
      simpa [u, Nat.add_assoc, if_pos (by omega)] using htail
    exact (summable_nat_add_iff 2).1 huTail
  · have hcof : ∀ᶠ k : ℕ in cofinite, 2 ≤ k := by
      refine Filter.mem_cofinite.mpr ?_
      simpa [Nat.not_le, Finset.mem_range] using
        (Finset.finite_toSet (Finset.range 2))
    filter_upwards [hcof] with k hk t ht
    have ht' : t ∈ Set.Ioo (-ε) ε := hK ht
    -- The higher-degree second-derivative bound already controls every cofinite coefficient.
    simpa [u, hk] using
      norm_iteratedDerivWithin_two_coeffSlice_le
        (Φ := Φ) (X := X) (H := H)
        (ε := ε) (ρ := ρ) (σ := σ)
        (t := t) (k := k)
        hk ht' hsliceOp

/-- Helper for Theorem 6.10: the full trace-power slice can be differentiated termwise up to
order `2` on the centered interval, so its second within-derivative is the `tsum` of the
coefficient-slice second within-derivatives. -/
private lemma fullSlice_iteratedDerivWithin_two_eq_tsum
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ σ : ℝ}
    (hρ : ρ ∈ Φ.scalarDom) (hε : 0 < ε)
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    iteratedDerivWithin 2
      (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
      (Set.Ioo (-ε) ε) 0 =
      ∑' k : ℕ,
        iteratedDerivWithin 2
          (fun t : ℝ ↦ Φ.coeff k * π[k] (X + t • H))
          (Set.Ioo (-ε) ε) 0 := by
  have h0I : (0 : ℝ) ∈ Set.Ioo (-ε) ε := zero_mem_centeredInterval hε
  -- Differentiate the full coefficient slice termwise; the finite degree-`0/1` head is harmless
  -- because the local-uniform hypotheses only need a cofinite tail bound.
  simpa using
    iteratedDerivWithin_tsum
      2
      isOpen_Ioo
      h0I
      (fun t ht ↦ (Φ.matrixFun_hasSum_powerTrace ((hsliceOp ht).1)).summable)
      (fun k hk1 hk2 ↦ by
        have hk : k = 1 ∨ k = 2 := by omega
        rcases hk with rfl | rfl
        · simpa using
            summableLocallyUniformlyOn_iteratedDerivWithin_one_coeffSlice
              (Φ := Φ) (X := X) (H := H) (ε := ε) (ρ := ρ) (σ := σ) hρ hsliceOp
        · simpa using
            summableLocallyUniformlyOn_iteratedDerivWithin_two_coeffSlice
              (Φ := Φ) (X := X) (H := H) (ε := ε) (ρ := ρ) (σ := σ) hρ hsliceOp)
      (fun m k r hk hr ↦
        differentiableAt_iteratedDerivWithin_coeffSlice
          (Φ := Φ) (X := X) (H := H) (ε := ε) (m := m) (a := k) hk hr)
/-- Helper for Theorem 6.10: at a domain point, the shifted trace-power tail is the full
spectral function minus the degree-`0` and degree-`1` trace-power head. -/
private lemma powerTraceTail_eq_matrixFun_sub_head_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (Y : SymmMat) (hY : Y ∈ Φ.dom) :
    (∑' m : ℕ, Φ.coeff (m + 2) * π[m + 2] Y) =
      Φ.matrixFun Y - (Φ.coeff 0 * π[0] Y + Φ.coeff 1 * π[1] Y) := by
  let f : ℕ → ℝ := fun k ↦ Φ.coeff k * π[k] Y
  have htail :
      HasSum (fun m : ℕ ↦ f (m + 2))
        (Φ.matrixFun Y - ∑ i ∈ Finset.range 2, f i) := by
    -- Reindex the convergent full trace-power series and isolate the degree-`0`/`1` head.
    exact (hasSum_nat_add_iff' 2).2 (Φ.matrixFun_hasSum_powerTrace hY)
  -- Expand the finite prefix into the explicit degree-`0` and degree-`1` terms used later.
  simpa [f, Finset.sum_range_succ, Finset.sum_range_one, add_assoc, add_left_comm, add_comm] using
    htail.tsum_eq

/-- Helper for Theorem 6.10: near a domain point, the shifted trace-power tail agrees with the
full spectral function minus its degree-`0` and degree-`1` trace-power head. -/
private lemma powerTraceTail_eq_matrixFun_sub_head_nhds_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X : SymmMat) (hX : X ∈ Φ.dom) :
    (fun Y : SymmMat ↦ ∑' m : ℕ, Φ.coeff (m + 2) * π[m + 2] Y) =ᶠ[nhds X]
      (fun Y : SymmMat ↦
        Φ.matrixFun Y - (Φ.coeff 0 * π[0] Y + Φ.coeff 1 * π[1] Y)) := by
  obtain ⟨ρ, hXρ, hρdom⟩ := exists_scalarWitness_gt_opNorm_of_mem_dom (Φ := Φ) X hX
  let toAmbientCLM :
      Mat →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap
  have hcontAmbientOp : Continuous fun A : Mat ↦ ambientOpNorm A := by
    -- Reuse the ambient Euclidean operator-norm continuity from the symmetric inclusion surface.
    by_cases hfin : IsEmpty (Fin n)
    · have hconst :
          (fun A : Mat ↦ ambientOpNorm A) = fun _ : Mat ↦ ambientOpNorm (0 : Mat) := by
        funext A
        have hA : A = 0 := Subsingleton.elim _ _
        simpa [hA]
      rw [hconst]
      exact continuous_const
    · letI : Nonempty (Fin n) := not_isEmpty_iff.mp hfin
      letI :
          Nontrivial (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := inferInstance
      have hcontCLM : Continuous fun A : Mat ↦ toAmbientCLM A :=
        LinearMap.continuous_of_finiteDimensional toAmbientCLM
      have hnormEq : (fun A : Mat ↦ ambientOpNorm A) = fun A : Mat ↦ ‖toAmbientCLM A‖ := by
        funext A
        simpa [toAmbientCLM, ambientOpNorm] using
          (Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A).symm
      rw [hnormEq]
      exact hcontCLM.norm
  have hcontSymmOp :
      Continuous fun Y : SymmMat ↦ ambientOpNorm (theoremSixTenSymmetricInclusion Y) := by
    -- The symmetric inclusion keeps the same operator-norm neighborhood control.
    simpa using hcontAmbientOp.comp theoremSixTenSymmetricInclusion.continuous
  have hOpNhds :
      (fun Y : SymmMat ↦ ambientOpNorm (theoremSixTenSymmetricInclusion Y)) ⁻¹' Set.Iio ρ ∈
        nhds X := by
    have hOpen :
        IsOpen ((fun Y : SymmMat ↦ ambientOpNorm (theoremSixTenSymmetricInclusion Y)) ⁻¹'
          Set.Iio ρ) :=
      hcontSymmOp.isOpen_preimage _ isOpen_Iio
    exact hOpen.mem_nhds (by simpa using hXρ)
  refine Filter.mem_of_superset hOpNhds ?_
  intro Y hY
  have hYdom : Y ∈ Φ.dom :=
    dom_of_opNorm_lt_scalarWitness (Φ := Φ) (Y := Y) hρdom (by simpa using hY)
  -- Inside the same operator-norm neighborhood, apply the pointwise head-tail decomposition.
  simpa using powerTraceTail_eq_matrixFun_sub_head_of_mem_dom (Φ := Φ) Y hYdom

/-- Helper for Theorem 6.10: on the centered interval supplied by the slice-domain witness, the
shifted trace-power tail slice is the full matrix-function slice minus the degree-`0`/`1` head. -/
private lemma powerTraceTailSlice_eq_matrixFunSlice_sub_head_onCenteredInterval
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ σ : ℝ}
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    Set.EqOn
      (fun t : ℝ ↦ ∑' m : ℕ, Φ.coeff (m + 2) * π[m + 2] (X + t • H))
      (fun t : ℝ ↦
        Φ.matrixFun (X + t • H) -
          (Φ.coeff 0 * π[0] (X + t • H) + Φ.coeff 1 * π[1] (X + t • H)))
      (Set.Ioo (-ε) ε) := by
  intro t ht
  have hXt : X + t • H ∈ Φ.dom := (hsliceOp ht).1
  -- Evaluate the pointwise tail decomposition at the translated slice point `X + t • H`.
  simpa using
    powerTraceTail_eq_matrixFun_sub_head_of_mem_dom
      (Φ := Φ) (Y := X + t • H) hXt

/-- Helper for Theorem 6.10: on any centered interval, the explicit degree-`0`/`1` head slice is
constant plus affine, so its second within-derivative at `0` vanishes. -/
private lemma powerTraceHeadSlice_iteratedDerivWithin_two_eq_zero
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε : ℝ}
    (h0I : (0 : ℝ) ∈ Set.Ioo (-ε) ε) :
    iteratedDerivWithin 2
      (fun t : ℝ ↦
        Φ.coeff 0 * π[0] (X + t • H) + Φ.coeff 1 * π[1] (X + t • H))
      (Set.Ioo (-ε) ε) 0 = 0 := by
  let head : SymmMat → ℝ := fun Y : SymmMat ↦
    Φ.coeff 0 * π[0] Y + Φ.coeff 1 * π[1] Y
  let headSlice : ℝ → ℝ := fun t : ℝ ↦ head (X + t • H)
  have hcontZero : ContDiffAt ℝ 2 (fun Y : SymmMat ↦ Φ.coeff 0 * π[0] Y) X := by
    -- The degree-zero trace term is smooth of all orders.
    exact (coeff_mul_powerTrace_contDiff (Φ := Φ) 0).contDiffAt
  have hcontOne : ContDiffAt ℝ 2 (fun Y : SymmMat ↦ Φ.coeff 1 * π[1] Y) X := by
    -- The degree-one trace term is likewise smooth of all orders.
    exact (coeff_mul_powerTrace_contDiff (Φ := Φ) 1).contDiffAt
  have hcontHead : ContDiffAt ℝ 2 head X := by
    -- The low-degree head is the sum of the smooth degree-zero and degree-one terms.
    simpa [head] using hcontZero.add hcontOne
  have hcontSliceZero :
      ContDiffAt ℝ 2 (fun t : ℝ ↦ Φ.coeff 0 * π[0] (X + t • H)) 0 := by
    -- Restrict the degree-zero term to the affine slice through `X`.
    simpa using
      ((coeffMulPowerTraceSlice_contDiffAll (Φ := Φ) (k := 0) X H).of_le
        (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)).contDiffAt
  have hcontSliceOne :
      ContDiffAt ℝ 2 (fun t : ℝ ↦ Φ.coeff 1 * π[1] (X + t • H)) 0 := by
    -- Restrict the degree-one term to the same affine slice.
    simpa using
      ((coeffMulPowerTraceSlice_contDiffAll (Φ := Φ) (k := 1) X H).of_le
        (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)).contDiffAt
  have hcontSlice : ContDiffAt ℝ 2 headSlice 0 := by
    -- The sliced head remains `C²`, so its within and ordinary second derivatives agree.
    simpa [head, headSlice] using hcontSliceZero.add hcontSliceOne
  have hwithin :
      iteratedDerivWithin 2 headSlice (Set.Ioo (-ε) ε) 0 = iteratedDeriv 2 headSlice 0 := by
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Ioo (-ε : ℝ) ε)
        hcontSlice
        h0I
  have hslice :
      iteratedDeriv 2 headSlice 0 = (iteratedFDeriv ℝ 2 head X) ![H, H] := by
    -- The ordinary second derivative of the head slice is the repeated-direction Hessian entry.
    simpa [head, headSlice] using
      slice_secondDeriv_eq_iteratedFDeriv_two (f := head) (X := X) (H := H) hcontHead
  have hheadIter : (iteratedFDeriv ℝ 2 head X) ![H, H] = 0 := by
    -- The degree-zero and degree-one head terms have vanishing Hessian, so their sum does too.
    rw [show head =
        (fun Y : SymmMat ↦ Φ.coeff 0 * π[0] Y) + (fun Y : SymmMat ↦ Φ.coeff 1 * π[1] Y) by
          funext Y
          simp [head]]
    rw [iteratedFDeriv_add_apply hcontZero hcontOne]
    simp [coeff_mul_powerTrace_iteratedFDeriv_two_eq_zero_zero,
      coeff_mul_powerTrace_iteratedFDeriv_two_eq_zero_one]
  -- Route correction: cancel the low-degree head on the scalar slice before returning to the
  -- matrix-level `tsum`; this keeps the remaining transport surface isolated.
  calc
    iteratedDerivWithin 2
        (fun t : ℝ ↦
          Φ.coeff 0 * π[0] (X + t • H) + Φ.coeff 1 * π[1] (X + t • H))
        (Set.Ioo (-ε) ε) 0
      = iteratedDeriv 2 headSlice 0 := by
          simpa [head, headSlice] using hwithin
    _ = (iteratedFDeriv ℝ 2 head X) ![H, H] := hslice
    _ = 0 := hheadIter

/-- Helper for Theorem 6.10: on a centered interval inside the matrix domain, the full trace-power
slice already has its second within-derivative equal to the `tsum` of the coefficient Hessian
entries at the base point. -/
private lemma fullSlice_iteratedDerivWithin_two_eq_tsum_coeff_hessians_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) {ε ρ σ : ℝ}
    (hρ : ρ ∈ Φ.scalarDom) (hε : 0 < ε)
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    iteratedDerivWithin 2
      (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
      (Set.Ioo (-ε) ε) 0 =
      ∑' k : ℕ, iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] := by
  let I : Set ℝ := Set.Ioo (-ε) ε
  let fullSlice : ℝ → ℝ := fun t : ℝ ↦
    ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H)
  let sliceSecondDerivTerm : ℕ → ℝ := fun k : ℕ ↦
    iteratedDerivWithin 2
      (fun t : ℝ ↦ Φ.coeff k * π[k] (X + t • H))
      I 0
  have h0I : (0 : ℝ) ∈ I := by
    -- The centered interval contains `0`, so the within-derivative identities can be evaluated there.
    simpa [I] using zero_mem_centeredInterval hε
  have hfull :
      iteratedDerivWithin 2 fullSlice I 0 = ∑' k : ℕ, sliceSecondDerivTerm k := by
    -- Exchange the full slice's second within-derivative with the convergent coefficient series.
    simpa [I, fullSlice, sliceSecondDerivTerm] using
      fullSlice_iteratedDerivWithin_two_eq_tsum
        (Φ := Φ) (X := X) (H := H) (ε := ε) (ρ := ρ) (σ := σ) hρ hε hsliceOp
  have hterm :
      sliceSecondDerivTerm =
        fun k : ℕ ↦ iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] := by
    -- Each coefficient slice already identifies its interior second within-derivative with the
    -- ambient repeated-direction Hessian entry at `X`.
    funext k
    simpa [I, sliceSecondDerivTerm] using
      iteratedDerivWithin_two_coeffSlice_eq_hessianAt
        (Φ := Φ) (X := X) (H := H) (k := k) (t := (0 : ℝ)) h0I
  -- Combine the termwise slice-to-Hessian identification with the termwise differentiation of the
  -- full slice.
  calc
    iteratedDerivWithin 2 fullSlice I 0 = ∑' k : ℕ, sliceSecondDerivTerm k := hfull
    _ = ∑' k : ℕ, iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] := by
      exact congrArg (fun g : ℕ → ℝ ↦ ∑' k : ℕ, g k) hterm

/-- Helper for Theorem 6.10: near a matrix-domain point, the full trace-power `tsum` and
`Φ.matrixFun` have the same repeated-direction second Fréchet derivative. -/
private lemma powerTraceTsum_iteratedFDeriv_two_apply_eq_matrixFun_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) (hX : X ∈ Φ.dom) :
    ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) =
      (iteratedFDeriv ℝ 2 Φ.matrixFun X) ![H, H] := by
  have hEqAt :
      Φ.matrixFun =ᶠ[nhds X] (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) :=
    matrixFun_eq_powerTraceTsum_nhds_of_mem_dom (Φ := Φ) X hX
  have hiter :
      iteratedFDeriv ℝ 2 Φ.matrixFun X =
        iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ hEqAt 2).eq_of_nhds
  -- Evaluate the neighborhood-stable second Fréchet derivative equality on the repeated direction
  -- `![H, H]`.
  exact congrArg (fun T ↦ T ![H, H]) hiter |>.symm

/-- Helper for Theorem 6.10: on the centered witness interval, the full trace-power slice should
already compute the repeated-direction second Fréchet derivative of the full trace-power `tsum`
at the base point. -/
private lemma fullSlice_iteratedDerivWithin_two_eq_powerTraceTsumIteratedFDeriv_two_of_contDiffAt
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat)
    {ε : ℝ} (hε : 0 < ε)
    (hcont :
      ContDiffAt ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) :
    iteratedDerivWithin 2
      (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
      (Set.Ioo (-ε) ε) 0 =
      ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) := by
  have h0I : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
    -- The centered interval contains `0`, so the within-derivative rewrites to the ordinary one.
    exact zero_mem_centeredInterval hε
  have hsliceCont :
      ContDiffAt ℝ 2
        (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
        0 := by
    have hlineCont : ContDiffAt ℝ 2 (fun t : ℝ ↦ X + t • H) 0 := by
      -- The affine slice is smooth of all orders.
      fun_prop
    -- Compose the full `tsum` with the affine line through `X`.
    simpa [Function.comp] using hcont.comp 0 hlineCont
  have hwithin :
      iteratedDerivWithin 2
        (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
        (Set.Ioo (-ε) ε) 0 =
      iteratedDeriv 2
        (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
        0 := by
    -- Interior differentiability lets the centered-interval second derivative collapse to the
    -- ordinary scalar second derivative at `0`.
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Ioo (-ε : ℝ) ε)
        hsliceCont
        h0I
  have hslice :
      iteratedDeriv 2
        (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
        0 =
      ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) := by
    -- The ordinary second derivative of the full scalar slice is the repeated-direction Hessian
    -- entry of the full `tsum`.
    simpa using
      slice_secondDeriv_eq_iteratedFDeriv_two
        (f := fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y)
        (X := X) (H := H) hcont
  -- Combine the within-to-ordinary rewrite with the slice/Hessian bridge.
  exact hwithin.trans hslice

/-- Helper for Theorem 6.10: on the centered witness interval, the full trace-power slice should
already compute the repeated-direction second Fréchet derivative of the full trace-power `tsum`
at the base point. -/
private lemma fullSlice_iteratedDerivWithin_two_eq_powerTraceTsumIteratedFDeriv_two_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) (hX : X ∈ Φ.dom)
    {ε ρ σ : ℝ} (hε : 0 < ε) (hρ : ρ ∈ Φ.scalarDom)
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    iteratedDerivWithin 2
      (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
      (Set.Ioo (-ε) ε) 0 =
      ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) := by
  -- Route correction: the remaining obstruction is no longer the tail/head transport. What is
  -- still missing is the owner-level bridge from the full centered slice second within-derivative
  -- to the matrix-side repeated-direction Hessian of the full `tsum`.
  have hcont :
      ContDiffAt ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X := by
    -- TODO: prove the full power-trace `tsum` is `C²` at `X` from the scalar witness `ρ` and the
    -- centered operator-norm control `hsliceOp`; this is the only remaining missing premise.
    have _ := hX
    have _ := hρ
    have _ := hsliceOp
    sorry
  -- Once the full `tsum` is `C²` at `X`, the centered slice/Hessian bridge is a generic
  -- within-to-ordinary derivative rewrite followed by the affine-line second-derivative formula.
  exact
    fullSlice_iteratedDerivWithin_two_eq_powerTraceTsumIteratedFDeriv_two_of_contDiffAt
      (Φ := Φ) (X := X) (H := H) (ε := ε) hε hcont

/-- Helper for Theorem 6.10: at a matrix-domain point, the full trace-power `tsum` should have its
repeated-direction second Fréchet derivative given by the termwise coefficient-Hessian series. -/
private lemma powerTraceTsum_iteratedFDeriv_two_eq_tsum_coeff_hessians_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) (hX : X ∈ Φ.dom) :
    ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) =
      ∑' k : ℕ, iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] := by
  -- Route correction: the scalar tail/head transport is already stabilized, so the only remaining
  -- blocker is the matrixFun Hessian bridge after the slice-level coefficient series is already known.
  obtain ⟨ε, ρ, σ, hε, hρ, hsliceOp⟩ :=
    existsCenteredSliceSubsetDomWithOpNormBound (Φ := Φ) X hX H
  have hsliceSeries :
      iteratedDerivWithin 2
        (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
        (Set.Ioo (-ε) ε) 0 =
        ∑' k : ℕ, iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] := by
    -- The scalar slice already differentiates termwise to the coefficient Hessian series.
    simpa using
      fullSlice_iteratedDerivWithin_two_eq_tsum_coeff_hessians_of_mem_dom
        (Φ := Φ) (X := X) (H := H) (ε := ε) (ρ := ρ) (σ := σ) hρ hε hsliceOp
  have hsliceHessian :
      iteratedDerivWithin 2
        (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
        (Set.Ioo (-ε) ε) 0 =
        ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) := by
    -- The only remaining bridge is the full-series slice/Hessian identification on the centered
    -- witness interval.
    simpa using
      fullSlice_iteratedDerivWithin_two_eq_powerTraceTsumIteratedFDeriv_two_of_mem_dom
        (Φ := Φ) (X := X) (H := H) hX (ε := ε) (ρ := ρ) (σ := σ) hε hρ hsliceOp
  -- Once the scalar full slice is identified with the matrix-level full `tsum` Hessian, the
  -- coefficient-series formula closes by transitivity.
  calc
    ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H])
        =
          iteratedDerivWithin 2
            (fun t : ℝ ↦ ∑' k : ℕ, Φ.coeff k * π[k] (X + t • H))
            (Set.Ioo (-ε) ε) 0 := by
              exact hsliceHessian.symm
    _ = ∑' k : ℕ, iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] :=
      hsliceSeries

/-- Helper for Theorem 6.10: after removing the degree-`0`/`1` head on the centered slice, the
remaining second within-derivative should match the full trace-power `tsum` Hessian entry at `X`.
-/
private lemma tailSliceSecondDeriv_eq_powerTraceTsumIteratedFDeriv_two_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat)
    (hX : X ∈ Φ.dom) {ε ρ σ : ℝ} (hε : 0 < ε) (hρ : ρ ∈ Φ.scalarDom)
    (hsliceOp :
      ∀ {u : ℝ}, u ∈ Set.Ioo (-ε) ε →
        X + u • H ∈ Φ.dom ∧ ‖(((X + u • H : SymmMat) : Mat))‖ < ρ ∧
          ‖(X + u • H : SymmMat)‖ < σ) :
    iteratedDerivWithin 2
      (fun t : ℝ ↦ ∑' m : ℕ, Φ.coeff (m + 2) * π[m + 2] (X + t • H))
      (Set.Ioo (-ε) ε) 0 =
      ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) := by
  let I : Set ℝ := Set.Ioo (-ε) ε
  let tailSlice : ℝ → ℝ := fun t : ℝ ↦
    ∑' m : ℕ, Φ.coeff (m + 2) * π[m + 2] (X + t • H)
  let A : ℕ → ℝ := fun k : ℕ ↦
    iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H]
  let tailSecondDerivTerm : ℕ → ℝ := fun m : ℕ ↦
    iteratedDerivWithin 2
      (fun t : ℝ ↦ Φ.coeff (m + 2) * π[m + 2] (X + t • H))
      I 0
  have h0I : (0 : ℝ) ∈ I := by
    simpa [I] using zero_mem_centeredInterval hε
  have htail_tsum :
      iteratedDerivWithin 2 tailSlice I 0 = ∑' m : ℕ, tailSecondDerivTerm m := by
    -- Exchange the second within-derivative with the shifted trace-power tail series.
    simpa [I, tailSlice, tailSecondDerivTerm] using
      iteratedDerivWithin_tsum
        2
        isOpen_Ioo
        h0I
        (fun t ht ↦ powerTrace_tail_summable_at_mem_dom (Φ := Φ) (X + t • H) ((hsliceOp ht).1))
        (fun k hk1 hk2 ↦ by
          have hk : k = 1 ∨ k = 2 := by omega
          rcases hk with rfl | rfl
          · simpa using
              summableLocallyUniformlyOn_iteratedDerivWithin_one_coeffSliceTail
                (Φ := Φ) (X := X) (H := H) (hρ := hρ) hsliceOp
          · simpa using
              summableLocallyUniformlyOn_iteratedDerivWithin_two_coeffSliceTail
                (Φ := Φ) (X := X) (H := H) (hρ := hρ) hsliceOp)
        (fun m k r hk hr ↦
          differentiableAt_iteratedDerivWithin_coeffSliceTail
            (Φ := Φ) (X := X) (H := H) (m := m) (a := k) hk hr)
  have hsummableTail :
      Summable tailSecondDerivTerm :=
    (summableLocallyUniformlyOn_iteratedDerivWithin_two_coeffSliceTail
      (Φ := Φ) (X := X) (H := H) (hρ := hρ) hsliceOp).summable h0I
  have htailHasSumRaw :
      HasSum tailSecondDerivTerm (iteratedDerivWithin 2 tailSlice I 0) := by
    -- Repackage the shifted scalar slice identity as a `HasSum` statement.
    simpa [htail_tsum] using hsummableTail.hasSum
  have htailTermEq :
      tailSecondDerivTerm = fun m : ℕ ↦ A (m + 2) := by
    -- Each tail summand already identifies its interior slice Hessian with the repeated-direction
    -- matrix Hessian entry at `X`.
    funext m
    simp [tailSecondDerivTerm, A, I]
    simpa [I] using
      iteratedDerivWithin_two_coeffSlice_eq_hessianAt
        (Φ := Φ) (X := X) (H := H) (k := m + 2) (t := (0 : ℝ)) h0I
  have htailHasSumScalar :
      HasSum (fun m : ℕ ↦ A (m + 2)) (iteratedDerivWithin 2 tailSlice I 0) := by
    -- Rewrite the scalar tail-derivative series into the matrix Hessian summands termwise.
    simpa [tailSecondDerivTerm, A] using (htailTermEq ▸ htailHasSumRaw)
  have hsummableA : Summable A := by
    -- A convergent shifted tail determines the full Hessian coefficient series up to the finite
    -- degree-`0/1` prefix.
    exact (summable_nat_add_iff 2).1 htailHasSumScalar.summable
  have hfullHasSumMatrix :
      HasSum A
        ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) := by
    -- The remaining matrix-side bridge rewrites the full `tsum` Hessian entry as the full
    -- coefficient-Hessian series.
    simpa [A] using
      (powerTraceTsum_iteratedFDeriv_two_eq_tsum_coeff_hessians_of_mem_dom
        (Φ := Φ) (X := X) (H := H) hX).symm ▸ hsummableA.hasSum
  have hheadPrefix :
      ∑ i ∈ Finset.range 2, A i = 0 := by
    -- The degree-`0` and degree-`1` Hessians vanish, so the finite prefix is zero.
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [A, coeff_mul_powerTrace_iteratedFDeriv_two_eq_zero_zero,
      coeff_mul_powerTrace_iteratedFDeriv_two_eq_zero_one]
  have htailHasSumMatrix :
      HasSum
        (fun m : ℕ ↦ A (m + 2))
        ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) := by
    -- Reindex the full coefficient-Hessian series back to the shifted tail once the zero head is
    -- restored explicitly.
    have hshifted :
        HasSum
          (fun m : ℕ ↦ A (m + 2))
          ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H] -
            ∑ i ∈ Finset.range 2, A i) := by
      simpa using (hasSum_nat_add_iff' 2).2 hfullHasSumMatrix
    simpa [hheadPrefix] using hshifted
  -- Route correction: compare the scalar tail slice and the matrix full `tsum` by identifying both
  -- as the sum of the same shifted coefficient-Hessian series.
  calc
    iteratedDerivWithin 2 tailSlice I 0 = ∑' m : ℕ, A (m + 2) := by
      exact htailHasSumScalar.tsum_eq.symm
    _ =
        ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) := by
          exact htailHasSumMatrix.tsum_eq

/-- Helper for Theorem 6.10: once the degree-`0`/`1` head is known to have zero Hessian, the
shifted tail terms already sum to the full trace-power `tsum` Hessian entry. -/
private lemma hasSum_powerTraceTail_iteratedFDeriv_two_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) (hX : X ∈ Φ.dom) :
    HasSum
      (fun m : ℕ ↦
        iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff (m + 2) * π[m + 2] Y) X ![H, H])
      ((iteratedFDeriv ℝ 2
          (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) := by
  obtain ⟨ε, ρ, σ, hε, hρ, hsliceOp⟩ :=
    existsCenteredSliceSubsetDomWithOpNormBound (Φ := Φ) X hX H
  have h0I : (0 : ℝ) ∈ Set.Ioo (-ε) ε := zero_mem_centeredInterval hε
  let tailSlice : ℝ → ℝ := fun t : ℝ ↦
    ∑' m : ℕ, Φ.coeff (m + 2) * π[m + 2] (X + t • H)
  have htail_tsum :
      iteratedDerivWithin 2 tailSlice (Set.Ioo (-ε) ε) 0 =
        ∑' m : ℕ,
          iteratedDerivWithin 2
            (fun t : ℝ ↦ Φ.coeff (m + 2) * π[m + 2] (X + t • H))
            (Set.Ioo (-ε) ε) 0 := by
    -- Exchange the second within-derivative with the shifted tail series on the centered slice.
    simpa [tailSlice] using
      iteratedDerivWithin_tsum
        2
        isOpen_Ioo
        h0I
        (fun t ht ↦ powerTrace_tail_summable_at_mem_dom (Φ := Φ) (X + t • H) ((hsliceOp ht).1))
        (fun k hk1 hk2 ↦ by
          have hk : k = 1 ∨ k = 2 := by omega
          rcases hk with rfl | rfl
          · simpa using
              summableLocallyUniformlyOn_iteratedDerivWithin_one_coeffSliceTail
                (Φ := Φ) (X := X) (H := H) (hρ := hρ) hsliceOp
          · simpa using
              summableLocallyUniformlyOn_iteratedDerivWithin_two_coeffSliceTail
                (Φ := Φ) (X := X) (H := H) (hρ := hρ) hsliceOp)
        (fun m k r hk hr ↦
          differentiableAt_iteratedDerivWithin_coeffSliceTail
            (Φ := Φ) (X := X) (H := H) (m := m) (a := k) hk hr)
  have hwithinHasSum :
      HasSum
        (fun m : ℕ ↦
          iteratedDerivWithin 2
            (fun t : ℝ ↦ Φ.coeff (m + 2) * π[m + 2] (X + t • H))
            (Set.Ioo (-ε) ε) 0)
        (iteratedDerivWithin 2 tailSlice (Set.Ioo (-ε) ε) 0) := by
    have hsummable :
        Summable
          (fun m : ℕ ↦
            iteratedDerivWithin 2
              (fun t : ℝ ↦ Φ.coeff (m + 2) * π[m + 2] (X + t • H))
              (Set.Ioo (-ε) ε) 0) :=
      (summableLocallyUniformlyOn_iteratedDerivWithin_two_coeffSliceTail
        (Φ := Φ) (X := X) (H := H) (hρ := hρ) hsliceOp).summable h0I
    -- Repackage the `tsum` identity as a `HasSum` statement for the within-derivative series.
    simpa [htail_tsum] using hsummable.hasSum
  have hterm_eq :
      (fun m : ℕ ↦
        Φ.coeff (m + 2) *
          iteratedDerivWithin 2
            (fun t : ℝ ↦ π[m + 2] (X + t • H))
            (Set.Ioo (-ε) ε) 0) =
        (fun m : ℕ ↦
          iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff (m + 2) * π[m + 2] Y) X ![H, H]) := by
    -- Each coefficient slice already identifies its interior second within-derivative with the
    -- repeated-direction Hessian quadratic form at the base point `X`.
    funext m
    simpa [smul_eq_mul] using
      iteratedDerivWithin_two_coeffSlice_eq_hessianAt
        (Φ := Φ) (X := X) (H := H) (k := m + 2) h0I
  have htarget :
      iteratedDerivWithin 2 tailSlice (Set.Ioo (-ε) ε) 0 =
        ((iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H]) := by
    -- Route correction: isolate the full-minus-head transport once, then reuse it as the sole
    -- target-value rewrite for the `HasSum` packaging.
    simpa [tailSlice] using
      tailSliceSecondDeriv_eq_powerTraceTsumIteratedFDeriv_two_of_mem_dom
        (Φ := Φ) (X := X) (H := H) hX (ε := ε) (ρ := ρ) (σ := σ) hε hρ
        hsliceOp
  -- Repackage the scalar within-derivative `HasSum` using the termwise Hessian identification and
  -- the single bridge from the centered tail slice to the full matrix-level `tsum`.
  simpa [hterm_eq, htarget] using hwithinHasSum
/-- Helper for Theorem 6.10: the degree-`0` and degree-`1` trace-power terms contribute no
repeated-direction second derivative, so the prefix sum over `range 2` vanishes. -/
private lemma powerTrace_head_secondDeriv_prefix_zero
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) :
    ∑ i ∈ Finset.range 2,
        iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff i * π[i] Y) X ![H, H] = 0 := by
  -- Only the `k = 0` and `k = 1` summands appear in `range 2`, and both Hessians vanish.
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [coeff_mul_powerTrace_iteratedFDeriv_two_eq_zero_zero,
    coeff_mul_powerTrace_iteratedFDeriv_two_eq_zero_one]
/-- Helper for Theorem 6.10: at every domain point, the ambient trace-power expansion has a
termwise second Fréchet derivative in repeated directions. -/
private lemma hasSum_powerTraceTsum_iteratedFDeriv_two_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X H : SymmMat) (hX : X ∈ Φ.dom) :
    HasSum
      (fun k : ℕ ↦ iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H])
      (iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X ![H, H]) := by
  let f : ℕ → ℝ := fun k : ℕ ↦
    iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H]
  have htail :
      HasSum (fun m : ℕ ↦ f (m + 2))
        (iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X ![H, H]) := by
    -- The shifted tail already packages to the full `tsum` Hessian once the head is cancelled.
    simpa [f] using
      hasSum_powerTraceTail_iteratedFDeriv_two_of_mem_dom (Φ := Φ) X H hX
  have hhead :
      ∑ i ∈ Finset.range 2, f i = 0 := by
    -- The low-degree prefix contributes no repeated-direction second derivative.
    simpa [f] using powerTrace_head_secondDeriv_prefix_zero (Φ := Φ) X H
  have hshifted :
      HasSum
        (fun m : ℕ ↦ f (m + 2))
        (iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X ![H, H] -
          ∑ i ∈ Finset.range 2, f i) := by
    -- Reinsert the explicit zero prefix so the standard shift lemma can undo the reindexing.
    simpa [hhead] using htail
  -- Undo the shift once the zero degree-`< 2` prefix has been restored.
  simpa [f] using (hasSum_nat_add_iff' 2).1 hshifted

/-- Helper for Theorem 6.10: near any matrix-domain point, `Φ.matrixFun` agrees with the ambient
trace-power `tsum` on a whole neighborhood, so second Fréchet derivatives can be rewritten
through the convergent power-trace expansion without reopening the spectral calculus. -/
private lemma matrixFun_eq_powerTraceTsum_nhds_of_mem_dom
    (Φ : AnalyticSymmetricSpectralFunction) (X : SymmMat) (hX : X ∈ Φ.dom) :
    Φ.matrixFun =ᶠ[nhds X] (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) := by
  obtain ⟨ρ, hXρ, hρdom⟩ := exists_scalarWitness_gt_opNorm_of_mem_dom (Φ := Φ) X hX
  let toAmbientCLM :
      Mat →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap
  have hcontAmbientOp : Continuous fun A : Mat ↦ ambientOpNorm A := by
    -- Express the ambient `L²` operator norm as the norm of a finite-dimensional linear image.
    by_cases hfin : IsEmpty (Fin n)
    · -- In the empty matrix size, every ambient matrix is definitionally zero, so the norm map is constant.
      have hconst :
          (fun A : Mat ↦ ambientOpNorm A) = fun _ : Mat ↦ ambientOpNorm (0 : Mat) := by
        funext A
        have hA : A = 0 := Subsingleton.elim _ _
        simpa [hA]
      rw [hconst]
      exact continuous_const
    · letI : Nonempty (Fin n) := not_isEmpty_iff.mp hfin
      letI :
          Nontrivial (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := inferInstance
      have hcontCLM : Continuous fun A : Mat ↦ toAmbientCLM A :=
        LinearMap.continuous_of_finiteDimensional toAmbientCLM
      have hnormEq : (fun A : Mat ↦ ambientOpNorm A) = fun A : Mat ↦ ‖toAmbientCLM A‖ := by
        funext A
        -- The ambient `L²` operator norm is exactly the norm of the bundled Euclidean action.
        simpa [toAmbientCLM, ambientOpNorm] using
          (Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A).symm
      rw [hnormEq]
      exact hcontCLM.norm
  have hcontSymmOp :
      Continuous fun Y : SymmMat ↦ ambientOpNorm (theoremSixTenSymmetricInclusion Y) := by
    -- Precompose the ambient continuity with the bundled symmetric inclusion used throughout the file.
    simpa using hcontAmbientOp.comp theoremSixTenSymmetricInclusion.continuous
  have hOpNhds :
      (fun Y : SymmMat ↦ ambientOpNorm (theoremSixTenSymmetricInclusion Y)) ⁻¹' Set.Iio ρ ∈
        nhds X := by
    have hOpen :
        IsOpen ((fun Y : SymmMat ↦ ambientOpNorm (theoremSixTenSymmetricInclusion Y)) ⁻¹'
          Set.Iio ρ) :=
      hcontSymmOp.isOpen_preimage _ isOpen_Iio
    exact hOpen.mem_nhds (by simpa using hXρ)
  refine Filter.mem_of_superset hOpNhds ?_
  intro Y hY
  -- Every point in the operator-norm neighborhood stays in `Φ.dom`, so the pointwise power-trace
  -- expansion of `Φ.matrixFun` applies and identifies the local `tsum`.
  have hYdom : Y ∈ Φ.dom :=
    dom_of_opNorm_lt_scalarWitness (Φ := Φ) (Y := Y) hρdom (by simpa using hY)
  exact (Φ.matrixFun_hasSum_powerTrace hYdom).tsum_eq.symm
end AnalyticSymmetricSpectralFunction

-- Proof sketch: the labeled theorem follows the source-facing power-series surface on the
-- coefficient sequence `a`, with the positive-radius, higher-degree coefficient nonnegativity,
-- and spectral-domain assumptions made explicit in Lean. The chapter owner
-- `AnalyticSymmetricSpectralFunction` remains an internal bridge, but is not part of the public
-- theorem surface. For the proof,
-- expand `theoremSixTenMatrixFun a` termwise as the trace-power series attached to `a`,
-- differentiate termwise on a neighborhood inside the spectral domain, apply the Chapter 6
-- power-trace Hessian estimate term-by-term, and resum to identify the coefficient sum with the
-- scalar second derivative of `theoremSixTenScalarFun a` at the eigenvalues of `|X|`.
-- Semantic search check: mathlib's `iteratedDeriv_eq_iteratedFDeriv` confirms the scalar
-- second-derivative owner used on the right-hand side.

/-- The scalar function attached to the source coefficient sequence of Theorem 6.10. -/
abbrev theoremSixTenScalarFun (a : ℕ → ℝ) : ℝ → ℝ :=
  FormalMultilinearSeries.ofScalarsSum a

/-- The matrix domain of Theorem 6.10: every eigenvalue lies in the scalar convergence ball. -/
def theoremSixTenDom (a : ℕ → ℝ) : Set SymmMat :=
  {X | ∀ i : Fin n,
    eigenvalues X i ∈ Metric.eball (0 : ℝ) ((FormalMultilinearSeries.ofScalars ℝ a).radius)}

/-- The spectral matrix function induced by the source coefficient sequence of Theorem 6.10. -/
def theoremSixTenMatrixFun (a : ℕ → ℝ) : SymmMat → ℝ :=
  fun X ↦ ∑ i : Fin n, theoremSixTenScalarFun a (eigenvalues X i)

/-- Theorem 6.10: if `a` defines a real power series with positive radius of convergence and
nonnegative coefficients in every degree `k ≥ 2`, then every `X` in the induced spectral domain
and every symmetric direction `H` satisfy the Hessian quadratic-form bound for the corresponding
spectral sum. -/
theorem hessianQuadraticForm_le_absEigenvalueSquareSum
    (a : ℕ → ℝ)
    (ha_radius : 0 < (FormalMultilinearSeries.ofScalars ℝ a).radius)
    (ha_nonneg : ∀ k : ℕ, 2 ≤ k → 0 ≤ a k)
    (X : SymmMat)
    (hX : X ∈ theoremSixTenDom a)
    (H : SymmMat) :
    (iteratedFDeriv ℝ 2 (theoremSixTenMatrixFun a) X) ![H, H] ≤
      ∑ i : Fin n,
        (iteratedDeriv 2 (theoremSixTenScalarFun a) (eigenvalues (|X| : SymmMat) i)) *
          ((eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ)) := by
  let Φ : AnalyticSymmetricSpectralFunction :=
    ⟨a, ha_radius, ha_nonneg⟩
  have hXΦ : X ∈ Φ.dom := by
    -- Repackage the source-facing domain hypothesis on `a` into the owner-level domain of `Φ`.
    rw [AnalyticSymmetricSpectralFunction.mem_dom_iff]
    intro i
    simpa [Φ, theoremSixTenDom, AnalyticSymmetricSpectralFunction.scalarDom] using hX i
  have hleft :
      HasSum
        (fun k : ℕ ↦ iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H])
        (iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X ![H, H]) :=
    AnalyticSymmetricSpectralFunction.hasSum_powerTraceTsum_iteratedFDeriv_two_of_mem_dom
      (Φ := Φ) X H hXΦ
  have habsX :
      ∀ i : Fin n, eigenvalues (|X| : SymmMat) i ∈ Φ.scalarDom :=
    AnalyticSymmetricSpectralFunction.intrinsicAbsEigenvalues_mem_scalarDom_of_mem_dom
      (Φ := Φ) X hXΦ
  have hright :
      HasSum
        (fun k : ℕ ↦
          Φ.coeff k *
            ((((k * (k - 1) : ℕ) : ℝ) *
              ∑ i : Fin n,
                (eigenvalues (|X| : SymmMat) i) ^ (k - 2) *
                  (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ))))
        (∑ i : Fin n,
          iteratedDeriv 2 Φ (eigenvalues (|X| : SymmMat) i) *
            (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ)) :=
    AnalyticSymmetricSpectralFunction.hasSum_intrinsicAbsEigenvalueSquareSeries
      (Φ := Φ) X H habsX
  have hterm :
      ∀ k : ℕ,
        iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] ≤
          Φ.coeff k *
            ((((k * (k - 1) : ℕ) : ℝ) *
              ∑ i : Fin n,
                (eigenvalues (|X| : SymmMat) i) ^ (k - 2) *
                  (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ))) := by
    intro k
    -- Compare the `k`th Hessian summand with the theorem's spectral majorant term-by-term.
    exact
      AnalyticSymmetricSpectralFunction.coeff_mul_powerTrace_iteratedFDeriv_two_le_intrinsicAbsEigenvaluePairing
        (Φ := Φ) k X H
  have hmatrix :
      theoremSixTenMatrixFun (n := n) a = AnalyticSymmetricSpectralFunction.matrixFun (n := n) Φ := by
    -- The public spectral function attached to `a` is definitionally the owner-level matrix
    -- function of the packaged coefficient sequence `Φ`.
    funext Y
    simp [Φ, theoremSixTenMatrixFun, theoremSixTenScalarFun,
      AnalyticSymmetricSpectralFunction.matrixFun, AnalyticSymmetricSpectralFunction.scalarFun]
  have hmatrixTsum :
      (iteratedFDeriv ℝ 2 Φ.matrixFun X) ![H, H] =
        (iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H] := by
    -- Rewrite the second Fréchet derivative through the neighborhood where `Φ.matrixFun` already
    -- agrees pointwise with its convergent trace-power expansion.
    have hEqAt :
        Φ.matrixFun =ᶠ[nhds X] (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) :=
      AnalyticSymmetricSpectralFunction.matrixFun_eq_powerTraceTsum_nhds_of_mem_dom
        (Φ := Φ) X hXΦ
    have hiter :
        iteratedFDeriv ℝ 2 Φ.matrixFun X =
          iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hEqAt 2).eq_of_nhds
    exact congrArg (fun T ↦ T ![H, H]) hiter
  -- Rewrite both sides through their convergent power-trace expansions and compare the two
  -- summable series term-by-term.
  calc
    (iteratedFDeriv ℝ 2 (theoremSixTenMatrixFun a) X) ![H, H]
        = (iteratedFDeriv ℝ 2 Φ.matrixFun X) ![H, H] := by
            rw [hmatrix]
    _ =
        (iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ ∑' k : ℕ, Φ.coeff k * π[k] Y) X) ![H, H] := by
            exact hmatrixTsum
    _ = ∑' k : ℕ, iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ Φ.coeff k * π[k] Y) X ![H, H] := by
            exact hleft.tsum_eq.symm
    _ ≤ ∑' k : ℕ,
          Φ.coeff k *
            ((((k * (k - 1) : ℕ) : ℝ) *
              ∑ i : Fin n,
                (eigenvalues (|X| : SymmMat) i) ^ (k - 2) *
                  (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ))) := by
          exact hleft.summable.tsum_le_tsum hterm hright.summable
    _ = ∑ i : Fin n,
          iteratedDeriv 2 (theoremSixTenScalarFun a) (eigenvalues (|X| : SymmMat) i) *
            (eigenvalues (|H| : SymmMat) i) ^ (2 : ℕ) := by
          rw [hright.tsum_eq]
          simp [Φ, theoremSixTenScalarFun, AnalyticSymmetricSpectralFunction.scalarFun]
