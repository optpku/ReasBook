/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_42

-- Declarations for this item will be appended below by the statement pipeline.

open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

noncomputable section

/- Definition 6.43 lies in the chapter's symmetric-matrix spectral-power-series domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` and `RealSymmetricMatrixSpace.eigenvalues`, the canonical symmetric-matrix and
  spectral owners already used throughout the chapter;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, the chapter owner for the
  trace-power coordinates of a symmetric matrix;
- mathlib `FormalMultilinearSeries.ofScalars`, `FormalMultilinearSeries.ofScalarsSum`, and
  `FormalMultilinearSeries.hasFPowerSeriesOnBall`, the canonical scalar power-series owner, its
  sum, and its convergence theorem on the open ball of radius `p.radius`.

Best owner abstraction:
- source-facing: a scalar power series with positive radius of convergence and coefficients
  nonnegative in degrees `k ≥ 2`, together with its induced spectral function on the natural
  matrix domain;
- core/canonical: `FormalMultilinearSeries.ofScalars ℝ coeff` and the chapter owners `𝕊^n`,
  `eigenvalues`, and `π[k]`;
- bridge/view: the scalar and matrix convergence domains together with the trace-power series
  expansion on `π[k]`.

Primitive data:
- a coefficient sequence `coeff : ℕ → ℝ`;
- a witness that the canonical scalar power series `FormalMultilinearSeries.ofScalars ℝ coeff`
  has strictly positive radius of convergence;
- the sign condition `0 ≤ coeff k` for all `k ≥ 2`.

Derived API:
- the genuine convergence radius `Φ.radius`;
- the scalar convergence domain `Φ.scalarDom`, used exactly where the canonical convergence API
  needs a domain membership witness for `FormalMultilinearSeries.ofScalarsSum Φ.coeff`;
- for each `n`, the matrix spectral domain `Φ.dom` together with the induced spectral sum
  `Φ.matrixFun X`;
- the bridge theorem that rewrites `Φ.matrixFun` as the Chapter 6 trace-power series in `π[k]`.

The previous version stored a free positive number called `radius`, defined the scalar function by
an unsupported global `tsum`, and then rebuilt a parallel matrix-level surface from that data. The
refinement below keeps the source-facing power-series object, but derives its radius and its
source domain and matrix spectral owner directly from mathlib's canonical scalar-series owner and
from the existing chapter spectral owners, without extra public aliases or proof-irrelevant domain
arguments in the public function surface.
-/

/-- An analytic symmetric spectral function for Definition 6.43 is given by a real power series
`f(τ) = a_0 + ∑_{k=1}^∞ a_k τ^k` whose genuine radius of convergence is positive and whose
coefficients are nonnegative for every degree `k ≥ 2`. It induces a scalar function on the open
interval of convergence and, for each `n`, a spectral function on the symmetric matrices whose
eigenvalues lie in that interval. -/
structure AnalyticSymmetricSpectralFunction where
  coeff : ℕ → ℝ
  has_pos_radius : 0 < (FormalMultilinearSeries.ofScalars ℝ coeff).radius
  coeff_nonneg (k : ℕ) (hk : 2 ≤ k) : 0 ≤ coeff k

namespace AnalyticSymmetricSpectralFunction

variable (Φ : AnalyticSymmetricSpectralFunction)

/-- The genuine radius of convergence of `Φ`. -/
abbrev radius : ENNReal :=
  (FormalMultilinearSeries.ofScalars ℝ Φ.coeff).radius

/-- The scalar convergence domain `(-Φ.radius, Φ.radius)`, written in the canonical `eball`
language used by mathlib's scalar-series API. -/
def scalarDom : Set ℝ :=
  Metric.eball (0 : ℝ) Φ.radius

/-- The scalar function induced by `Φ` is the canonical sum of its scalar formal power series. -/
def scalarFun : ℝ → ℝ :=
  FormalMultilinearSeries.ofScalarsSum Φ.coeff

/-- An analytic symmetric spectral function can be evaluated as its induced scalar function. -/
instance : CoeFun AnalyticSymmetricSpectralFunction (fun _ ↦ ℝ → ℝ) where
  coe Φ := Φ.scalarFun

/-- The induced matrix spectral domain: every eigenvalue lies in the scalar convergence domain. -/
def dom {n : ℕ} : Set (𝕊^n) :=
  {X | ∀ i : Fin n, eigenvalues X i ∈ Φ.scalarDom}

/-- The spectral function induced by `Φ`. Its natural source-domain restriction is recorded
separately by `Φ.dom`; the underlying scalar-series owner is the total canonical sum
`FormalMultilinearSeries.ofScalarsSum Φ.coeff`. -/
def matrixFun {n : ℕ} (X : 𝕊^n) : ℝ :=
  ∑ i : Fin n, FormalMultilinearSeries.ofScalarsSum Φ.coeff (eigenvalues X i)

/-- The canonical radius of convergence attached to `Φ` is strictly positive. -/
theorem radius_pos : 0 < Φ.radius :=
  Φ.has_pos_radius

/-- The scalar function of `Φ` is represented by its canonical scalar formal power series on the
open ball of radius `Φ.radius`. -/
theorem hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall
      (FormalMultilinearSeries.ofScalarsSum Φ.coeff)
      (FormalMultilinearSeries.ofScalars ℝ Φ.coeff)
      0
      Φ.radius := by
  simpa [radius] using
    (FormalMultilinearSeries.ofScalars ℝ Φ.coeff).hasFPowerSeriesOnBall Φ.radius_pos

/-- The scalar function attached to `Φ` has the expected convergent power-series expansion at every
point of the scalar domain. -/
theorem scalar_hasSum {τ : ℝ} (hτ : τ ∈ Φ.scalarDom) :
    HasSum (fun k : ℕ ↦ Φ.coeff k * τ ^ k) (Φ τ) := by
  simpa [smul_eq_mul, mul_comm] using
    FormalMultilinearSeries.hasSum (FormalMultilinearSeries.ofScalars ℝ Φ.coeff) hτ

/-- Evaluating `Φ` as a function returns the canonical scalar-series sum attached to its
coefficients. -/
@[simp] theorem coe_apply (τ : ℝ) :
    Φ τ = FormalMultilinearSeries.ofScalarsSum Φ.coeff τ :=
  rfl

@[simp] theorem mem_dom_iff {n : ℕ} {X : 𝕊^n} :
    X ∈ Φ.dom ↔ ∀ i : Fin n, eigenvalues X i ∈ Φ.scalarDom :=
  Iff.rfl

@[simp] theorem matrixFun_apply {n : ℕ} {X : 𝕊^n} :
    Φ.matrixFun X = ∑ i : Fin n, FormalMultilinearSeries.ofScalarsSum Φ.coeff (eigenvalues X i) :=
  rfl

/-- Helper for Definition 6.43: tracing the Hermitian functional calculus of a symmetric matrix
applies the scalar function to the ordered eigenvalues and sums the result. -/
private theorem traceCfc_eq_sumMapEigenvalues
    {n : ℕ} (Q : 𝕊^n) (f : ℝ → ℝ) :
    Matrix.trace ((isHermitian Q).cfc f) = ∑ i : Fin n, f (eigenvalues Q i) := by
  -- Rewrite the functional calculus in an eigenbasis so the trace becomes the diagonal sum.
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp]

/-- Helper for Definition 6.43: the Chapter 6 trace-power owner `π[k]` is the sum of the `k`-th
powers of the ordered eigenvalues. -/
private theorem powerTrace_eq_sumEigenvaluePowers
    {n : ℕ} (k : ℕ) (X : 𝕊^n) :
    π[k] X = ∑ i : Fin n, (eigenvalues X i) ^ k := by
  -- Rewrite `π[k]` as an ambient trace, then identify that trace with Hermitian functional
  -- calculus for `x ↦ x^k`.
  calc
    π[k] X = Matrix.trace (((X : Matrix (Fin n) (Fin n) ℝ) ^ k)) := by
      rw [RealSymmetricMatrixSpace.powerTrace_def]
    _ = Matrix.trace (cfc (fun x : ℝ ↦ x ^ k) (X : Matrix (Fin n) (Fin n) ℝ)) := by
          congr 1
          symm
          simpa using
            cfc_pow_id (X : Matrix (Fin n) (Fin n) ℝ) k
              (isHermitian X : IsSelfAdjoint (X : Matrix (Fin n) (Fin n) ℝ))
    _ = Matrix.trace ((isHermitian X).cfc (fun x : ℝ ↦ x ^ k)) := by
          rw [(isHermitian X).cfc_eq]
    _ = ∑ i : Fin n, (eigenvalues X i) ^ k := by
          rw [traceCfc_eq_sumMapEigenvalues]

/-- Helper for Definition 6.43: summing the scalar power-series expansions over the finitely many
eigenvalues of `X` produces the matrix spectral value `Φ.matrixFun X`. -/
private theorem matrixFun_hasSum_eigenvaluePowers
    {n : ℕ} {X : 𝕊^n} (hX : X ∈ Φ.dom) :
    HasSum (fun k : ℕ ↦ ∑ i : Fin n, Φ.coeff k * (eigenvalues X i) ^ k) (Φ.matrixFun X) := by
  have hscalar :
      ∀ i : Fin n, HasSum (fun k : ℕ ↦ Φ.coeff k * (eigenvalues X i) ^ k) (Φ (eigenvalues X i)) :=
    fun i ↦ Φ.scalar_hasSum (hX i)
  -- Assemble the scalar series over the finite eigenvalue index set by induction on the finset.
  have hpartial :
      ∀ s : Finset (Fin n),
        HasSum
          (fun k : ℕ ↦ s.sum (fun i ↦ Φ.coeff k * (eigenvalues X i) ^ k))
          (s.sum fun i ↦ Φ (eigenvalues X i)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi hs
      -- Add the scalar expansion for the new eigenvalue to the already assembled partial sum.
      have hiSeries := hscalar i
      have hsum := hiSeries.add hs
      simpa [Finset.sum_insert, hi, add_comm, add_left_comm, add_assoc] using hsum
  -- The full finite sum over `Fin n` is exactly `Φ.matrixFun X`.
  simpa [matrixFun_apply, coe_apply] using hpartial Finset.univ

-- Proof sketch: for each eigenvalue `λᵢ(X)`, use `scalar_hasSum` on the scalar-domain witness
-- coming from `hX i`; summing over `i` and exchanging the finite spectral sum with the convergent
-- scalar series identifies the resulting coefficient of degree `k` with
-- `a_k * ∑ᵢ λᵢ(X)^k = a_k * π_k(X)`.
/-- Definition 6.43: the matrix spectral function of `Φ` is the Chapter 6 trace-power series
attached to the owner `π[k]`. This is the thin bridge from the source-facing spectral sum to the
existing trace-power owners. -/
theorem matrixFun_hasSum_powerTrace {n : ℕ} {X : 𝕊^n} (hX : X ∈ Φ.dom) :
    HasSum (fun k : ℕ ↦ Φ.coeff k * π[k] X) (Φ.matrixFun X) := by
  -- First assemble the scalar power-series expansions over the ordered eigenvalues of `X`.
  have hseries := Φ.matrixFun_hasSum_eigenvaluePowers hX
  have hrewritten :
      HasSum
        (fun k : ℕ ↦ Φ.coeff k * ∑ i : Fin n, (eigenvalues X i) ^ k)
        (Φ.matrixFun X) := by
    -- Factor the common coefficient `Φ.coeff k` out of the finite eigenvalue sum.
    convert hseries using 1
    ext k
    symm
    exact
      (Finset.mul_sum (s := Finset.univ) (f := fun i : Fin n ↦ (eigenvalues X i) ^ k)
        (a := Φ.coeff k)).symm
  -- Replace the eigenvalue power sum with the chapter owner `π[k]`.
  simpa [powerTrace_eq_sumEigenvaluePowers] using hrewritten

end AnalyticSymmetricSpectralFunction
