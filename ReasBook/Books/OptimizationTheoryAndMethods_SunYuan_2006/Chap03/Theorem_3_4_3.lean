/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_23
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open scoped BigOperators

-- Domain sampling:
-- * source-facing owner here: the forward mixed-difference Hessian matrix on `ℝ^n`
-- * core/canonical owner already in the project: `hessianAt`
-- * bridge/view used here: the Euclidean matrix representation of `hessianAt`
--   via `Matrix.toEuclideanCLM`
-- * canonical standard basis owner reused from nearby Chapter 3 files: `EuclideanSpace.basisFun`
-- * Chapter 1 owners reused unchanged: `‖·‖₁`, `‖·‖∞`, `‖·‖_F`

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Hessian" => Matrix (Fin n) (Fin n) ℝ
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/-- The forward mixed second-difference matrix with common step `h`. -/
def finiteDifferenceHessianMatrix (f : Point → ℝ) (x : Point) (h : ℝ) : Hessian :=
  fun i j ↦
    (f (x + h • e i + h • e j) -
        f (x + h • e i) -
        f (x + h • e j) +
        f x) / (h ^ (2 : ℕ))

/-- The Hessian matrix of `f` at `x`, obtained from the canonical Hessian owner `hessianAt`
through the standard Euclidean matrix equivalence. -/
abbrev hessianMatrixAt (f : Point → ℝ) (x : Point) : Hessian :=
  (Matrix.toEuclideanCLM : Hessian ≃⋆ₐ[ℝ] Point →L[ℝ] Point).symm (hessianAt f x)

/-- Converting `hessianMatrixAt f x` back to a continuous linear map recovers `hessianAt f x`. -/
theorem toEuclideanCLM_hessianMatrixAt (f : Point → ℝ) (x : Point) :
    (Matrix.toEuclideanCLM : Hessian ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (hessianMatrixAt f x) =
      hessianAt f x := by
  simp [hessianMatrixAt]

section Theorem343

variable (D : Set Point) (f : Point → ℝ) (x : Point) (h : ℝ) (γ : NNReal)
variable
  (hD_open : IsOpen D)
  (hD_convex : Convex ℝ D)
  (hx : x ∈ D)
  (hf : ContDiffOn ℝ 2 f D)
  (h_hessian_lipschitz :
    ∀ y ∈ D,
      ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ (γ : ℝ) * ‖y - x‖)
  (hh : 0 < h)
  (h_forward_step_mem : ∀ i : Fin n, x + h • e i ∈ D)

/-- Helper for Chapter03 Theorem 3.4.3: at a `C²` point, the Hessian operator evaluated against a
test vector agrees with the second iterated Fréchet derivative. -/
lemma inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt
    {f : Point → ℝ} {x y z : Point}
    (hC2 : ContDiffAt ℝ 2 f x) :
    inner ℝ z (hessianAt f x y) = (iteratedFDeriv ℝ 2 f x) ![y, z] := by
  let e' : StrongDual ℝ Point ≃L[ℝ] Point :=
    (InnerProductSpace.toDual ℝ Point).symm.toContinuousLinearEquiv
  -- Differentiate `fderiv ℝ f` once and transport it through the Riesz map defining `gradient`.
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    (hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hgrad := by
    simpa [gradient, Function.comp, e'] using ((e'.hasFDerivAt).comp x hfd)
  have hgrad' :
      fderiv ℝ (gradient f) x = e'.toContinuousLinearMap ∘SL fderiv ℝ (fderiv ℝ f) x :=
    (show HasFDerivAt (gradient f) _ x from hgrad).fderiv
  have hyEq :
      hessianAt f x y = e' ((fderiv ℝ (fderiv ℝ f) x) y) := by
    simpa [hessianAt, e'] using congrArg (fun T : Point →L[ℝ] Point => T y) hgrad'
  calc
    inner ℝ z (hessianAt f x y) = inner ℝ z (e' ((fderiv ℝ (fderiv ℝ f) x) y)) := by
      rw [hyEq]
    _ = ((fderiv ℝ (fderiv ℝ f) x) y) z := by
      rw [real_inner_comm]
      change
        inner ℝ (((InnerProductSpace.toDual ℝ Point).symm) ((fderiv ℝ (fderiv ℝ f) x) y)) z =
          ((fderiv ℝ (fderiv ℝ f) x) y) z
      simp
    _ = (iteratedFDeriv ℝ 2 f x) ![y, z] := by
      symm
      exact iteratedFDeriv_two_apply f x ![y, z]

/-- Helper for Chapter03 Theorem 3.4.3: the Euclidean Hessian-matrix entry is the corresponding
coordinate of the second iterated Fréchet derivative. -/
lemma hessianMatrixAt_entry_eq_iteratedFDeriv_basis
    {f : Point → ℝ} {x : Point}
    (hC2 : ContDiffAt ℝ 2 f x) (i j : Fin n) :
    hessianMatrixAt f x i j = (iteratedFDeriv ℝ 2 f x) ![e j, e i] := by
  -- Convert the matrix entry to the bilinear Hessian pairing, then invoke the local Hessian bridge.
  calc
    hessianMatrixAt f x i j =
        inner ℝ (e i)
          (((Matrix.toEuclideanCLM : Hessian ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
            (hessianMatrixAt f x)) (e j)) := by
          have hentry := (Matrix.inner_toEuclideanCLM (hessianMatrixAt f x) (e i) (e j)).symm
          simpa [Matrix.dotProduct_mulVec, EuclideanSpace.basisFun_apply] using hentry
    _ = inner ℝ (e i) (hessianAt f x (e j)) := by
      rw [toEuclideanCLM_hessianMatrixAt]
    _ = (iteratedFDeriv ℝ 2 f x) ![e j, e i] := by
      exact inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt (f := f) (x := x)
        (y := e j) (z := e i) hC2

/-- Helper for Chapter03 Theorem 3.4.3: at a `C²` point, the second iterated Fréchet derivative is
symmetric in its two slots. -/
lemma iteratedFDeriv_swap_of_contDiffAt
    {f : Point → ℝ} {x y z : Point}
    (hC2 : ContDiffAt ℝ 2 f x) :
    (iteratedFDeriv ℝ 2 f x) ![y, z] = (iteratedFDeriv ℝ 2 f x) ![z, y] := by
  -- Transfer symmetry from the standard `C²` second-derivative theorem to the concrete `![y, z]`
  -- evaluation used below.
  exact
    (hC2.isSymmSndFDerivAt (n := 2) (by simp)).iteratedFDeriv_cons (x := x) (v := y) (w := z)

/-- Helper for Chapter03 Theorem 3.4.3: a mixed coordinate step pulls the common scalar `h`
out of both multilinear slots, contributing a factor `h²`. -/
lemma mixed_coordinate_step_hessian_eval
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Point) ℝ)
    (h : ℝ) (i j : Fin n) :
    A ![h • e i, h • e j] = h ^ 2 * A ![e i, e j] := by
  have hscaled : (![h • e i, h • e j] : Fin 2 → Point) =
      fun k : Fin 2 ↦ (![h, h] : Fin 2 → ℝ) k • (![e i, e j] : Fin 2 → Point) k := by
    ext k
    fin_cases k <;> rfl
  -- Pull the common scalar out of both coordinates at once.
  rw [hscaled]
  simpa [pow_two] using (A.map_smul_univ (![h, h] : Fin 2 → ℝ) (![e i, e j] : Fin 2 → Point))

/-- Helper for Chapter03 Theorem 3.4.3: expanding the quadratic term on `u + v` yields the two
diagonal contributions and the two mixed contributions. -/
lemma quadratic_expand
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Point) ℝ)
    (u v : Point) :
    A ![u + v, u + v] = A ![u, u] + A ![u, v] + A ![v, u] + A ![v, v] := by
  have hleft :
      (![u + v, u + v] : Fin 2 → Point) = Fin.cons (u + v) (fun _ : Fin 1 ↦ u + v) := by
    ext k
    fin_cases k <;> rfl
  have hu : (![u, u + v] : Fin 2 → Point) = Fin.cons u (fun _ : Fin 1 ↦ u + v) := by
    ext k
    fin_cases k <;> rfl
  have hv : (![v, u + v] : Fin 2 → Point) = Fin.cons v (fun _ : Fin 1 ↦ u + v) := by
    ext k
    fin_cases k <;> rfl
  have hu' : (![u, u + v] : Fin 2 → Point) = Fin.snoc (fun _ : Fin 1 ↦ u) (u + v) := by
    ext k
    fin_cases k <;> rfl
  have huu : (![u, u] : Fin 2 → Point) = Fin.snoc (fun _ : Fin 1 ↦ u) u := by
    ext k
    fin_cases k <;> rfl
  have huv : (![u, v] : Fin 2 → Point) = Fin.snoc (fun _ : Fin 1 ↦ u) v := by
    ext k
    fin_cases k <;> rfl
  have hv' : (![v, u + v] : Fin 2 → Point) = Fin.snoc (fun _ : Fin 1 ↦ v) (u + v) := by
    ext k
    fin_cases k <;> rfl
  have hvu : (![v, u] : Fin 2 → Point) = Fin.snoc (fun _ : Fin 1 ↦ v) u := by
    ext k
    fin_cases k <;> rfl
  have hvv : (![v, v] : Fin 2 → Point) = Fin.snoc (fun _ : Fin 1 ↦ v) v := by
    ext k
    fin_cases k <;> rfl
  -- Expand once in the first coordinate and once in the second coordinate.
  calc
    A ![u + v, u + v] = A ![u, u + v] + A ![v, u + v] := by
      rw [hleft, hu, hv]
      simpa using A.toMultilinearMap.cons_add (m := fun _ : Fin 1 ↦ u + v) (x := u) (y := v)
    _ = (A ![u, u] + A ![u, v]) + (A ![v, u] + A ![v, v]) := by
      rw [hu', huu, huv, hv', hvu, hvv]
      congr 1
      · simpa using A.toMultilinearMap.snoc_add (m := fun _ : Fin 1 ↦ u) (x := u) (y := v)
      · simpa using A.toMultilinearMap.snoc_add (m := fun _ : Fin 1 ↦ v) (x := u) (y := v)
    _ = A ![u, u] + A ![u, v] + A ![v, u] + A ![v, v] := by ring

/-- Helper for Chapter03 Theorem 3.4.3: the mixed quadratic Taylor term is exactly `h²` times the
`(i,j)` Hessian entry. -/
lemma mixed_coordinate_quadratic_term_eq_hsq_mul_hessian_entry
    {f : Point → ℝ} {x : Point}
    (hC2 : ContDiffAt ℝ 2 f x) (h : ℝ) (i j : Fin n) :
    ((1 / 2 : ℝ) *
        ((iteratedFDeriv ℝ 2 f x) ![h • e i + h • e j, h • e i + h • e j] -
          (iteratedFDeriv ℝ 2 f x) ![h • e i, h • e i] -
          (iteratedFDeriv ℝ 2 f x) ![h • e j, h • e j])) =
      h ^ (2 : ℕ) * hessianMatrixAt f x i j := by
  let A := iteratedFDeriv ℝ 2 f x
  have hquad := quadratic_expand A (h • e i) (h • e j)
  have hmix : A ![h • e i, h • e j] = h ^ 2 * hessianMatrixAt f x i j := by
    -- Normalize the mixed multilinear term to the Hessian entry through symmetry.
    calc
      A ![h • e i, h • e j] = h ^ 2 * A ![e i, e j] := mixed_coordinate_step_hessian_eval A h i j
      _ = h ^ 2 * A ![e j, e i] := by rw [iteratedFDeriv_swap_of_contDiffAt hC2]
      _ = h ^ 2 * hessianMatrixAt f x i j := by
        rw [hessianMatrixAt_entry_eq_iteratedFDeriv_basis hC2 i j]
  have hmix' : A ![h • e j, h • e i] = h ^ 2 * hessianMatrixAt f x i j := by
    calc
      A ![h • e j, h • e i] = A ![h • e i, h • e j] := by
        rw [iteratedFDeriv_swap_of_contDiffAt hC2]
      _ = h ^ 2 * hessianMatrixAt f x i j := hmix
  have hcore :
      A ![h • e i + h • e j, h • e i + h • e j] - A ![h • e i, h • e i] -
          A ![h • e j, h • e j] =
        2 * (h ^ 2 * hessianMatrixAt f x i j) := by
    rw [hquad, hmix, hmix']
    ring
  -- The `1 / 2` prefactor removes the duplicated mixed contribution.
  rw [hcore]
  ring

-- Route correction: the alpha-beta-eta argument was already correct locally, but the late helper
-- layer leaked section-generalized `Point`/`e` shorthand into exported types. The remaining
-- declarations below therefore spell out the public binders explicitly while keeping the textbook
-- proof route unchanged.
/-- Helper for Chapter03 Theorem 3.4.3: the textbook `α - β - η` cancellation identity is exactly
the scaled forward mixed-difference error. -/
lemma finiteDifferenceHessian_scaled_entry_error_eq_alpha_sub_beta_sub_eta
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (h : ℝ) (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hf : ContDiffOn ℝ 2 f D)
    (h_hessian_lipschitz :
      ∀ y ∈ D,
        ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ (γ : ℝ) * ‖y - x‖)
    (hh : 0 < h)
    (h_forward_step_mem :
      ∀ i : Fin n, x + h • EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (hC2 : ContDiffAt ℝ 2 f x)
    (h_mixed_step_mem :
      ∀ i : Fin n, ∀ j : Fin n,
        x + h • EuclideanSpace.basisFun (Fin n) ℝ i +
          h • EuclideanSpace.basisFun (Fin n) ℝ j ∈ D)
    (i j : Fin n) :
    h ^ (2 : ℕ) * (finiteDifferenceHessianMatrix f x h i j - hessianMatrixAt f x i j) =
      (f (x + h • EuclideanSpace.basisFun (Fin n) ℝ i +
            h • EuclideanSpace.basisFun (Fin n) ℝ j) - f x -
          fderiv ℝ f x
            (h • EuclideanSpace.basisFun (Fin n) ℝ i +
              h • EuclideanSpace.basisFun (Fin n) ℝ j) -
          (1 / 2 : ℝ) *
            (iteratedFDeriv ℝ 2 f x) ![
              h • EuclideanSpace.basisFun (Fin n) ℝ i +
                h • EuclideanSpace.basisFun (Fin n) ℝ j,
              h • EuclideanSpace.basisFun (Fin n) ℝ i +
                h • EuclideanSpace.basisFun (Fin n) ℝ j]) -
        (f (x + h • EuclideanSpace.basisFun (Fin n) ℝ i) - f x -
          fderiv ℝ f x (h • EuclideanSpace.basisFun (Fin n) ℝ i) -
          (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![
            h • EuclideanSpace.basisFun (Fin n) ℝ i,
            h • EuclideanSpace.basisFun (Fin n) ℝ i]) -
        (f (x + h • EuclideanSpace.basisFun (Fin n) ℝ j) - f x -
          fderiv ℝ f x (h • EuclideanSpace.basisFun (Fin n) ℝ j) -
          (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![
            h • EuclideanSpace.basisFun (Fin n) ℝ j,
            h • EuclideanSpace.basisFun (Fin n) ℝ j]) := by
  let basis : Fin n → EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ
  -- Expand the finite difference and isolate the quadratic Taylor correction.
  have hquad :=
    mixed_coordinate_quadratic_term_eq_hsq_mul_hessian_entry
      (f := f) (x := x) hC2 h i j
  let a : ℝ := f (x + h • basis i + h • basis j)
  let b : ℝ := f (x + h • basis i)
  let c : ℝ := f (x + h • basis j)
  let d : ℝ := f x
  have hquot :
      h ^ (2 : ℕ) * finiteDifferenceHessianMatrix f x h i j =
        a - b - c + d := by
    -- First abbreviate the four scalar samples so only the `h² / h²` cancellation remains.
    simp [a, b, c, d, basis, finiteDifferenceHessianMatrix]
    field_simp [hh.ne']
  calc
    h ^ (2 : ℕ) * (finiteDifferenceHessianMatrix f x h i j - hessianMatrixAt f x i j)
        =
          a - b - c + d -
            h ^ (2 : ℕ) * hessianMatrixAt f x i j := by
          rw [mul_sub, hquot]
    _ =
        (f (x + h • basis i + h • basis j) - f x -
            fderiv ℝ f x (h • basis i + h • basis j) -
            (1 / 2 : ℝ) *
              (iteratedFDeriv ℝ 2 f x) ![h • basis i + h • basis j, h • basis i + h • basis j]) -
          (f (x + h • basis i) - f x -
            fderiv ℝ f x (h • basis i) -
            (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i, h • basis i]) -
        (f (x + h • basis j) - f x -
          fderiv ℝ f x (h • basis j) -
          (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis j, h • basis j]) := by
          -- The linear terms cancel by additivity and the quadratic terms collapse to the
          -- mixed Hessian entry through the previous helper.
          simp [a, b, c, d, basis, ← hquad, map_add]
          ring

/-- Helper for Chapter03 Theorem 3.4.3: the three Taylor remainders from the textbook
`α, β, η` combine into the explicit `5γh³/3` bound. -/
lemma finiteDifferenceHessian_alpha_beta_eta_combined_bound
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (h : ℝ) (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hf : ContDiffOn ℝ 2 f D)
    (h_hessian_lipschitz :
      ∀ y ∈ D,
        ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ (γ : ℝ) * ‖y - x‖)
    (hh : 0 < h)
    (h_forward_step_mem :
      ∀ i : Fin n, x + h • EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (h_mixed_step_mem :
      ∀ i : Fin n, ∀ j : Fin n,
        x + h • EuclideanSpace.basisFun (Fin n) ℝ i +
          h • EuclideanSpace.basisFun (Fin n) ℝ j ∈ D)
    (i j : Fin n) :
    |(f (x + h • EuclideanSpace.basisFun (Fin n) ℝ i +
          h • EuclideanSpace.basisFun (Fin n) ℝ j) - f x -
        fderiv ℝ f x
          (h • EuclideanSpace.basisFun (Fin n) ℝ i +
            h • EuclideanSpace.basisFun (Fin n) ℝ j) -
        (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![
          h • EuclideanSpace.basisFun (Fin n) ℝ i +
            h • EuclideanSpace.basisFun (Fin n) ℝ j,
          h • EuclideanSpace.basisFun (Fin n) ℝ i +
            h • EuclideanSpace.basisFun (Fin n) ℝ j]) -
      (f (x + h • EuclideanSpace.basisFun (Fin n) ℝ i) - f x -
        fderiv ℝ f x (h • EuclideanSpace.basisFun (Fin n) ℝ i) -
        (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![
          h • EuclideanSpace.basisFun (Fin n) ℝ i,
          h • EuclideanSpace.basisFun (Fin n) ℝ i]) -
      (f (x + h • EuclideanSpace.basisFun (Fin n) ℝ j) - f x -
        fderiv ℝ f x (h • EuclideanSpace.basisFun (Fin n) ℝ j) -
        (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![
          h • EuclideanSpace.basisFun (Fin n) ℝ j,
          h • EuclideanSpace.basisFun (Fin n) ℝ j])| ≤
      ((5 : ℝ) / 3) * (γ : ℝ) * h ^ (3 : ℕ) := by
  let basis : Fin n → EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ
  let α : ℝ :=
    f (x + (h • basis i + h • basis j)) -
      (f x +
        fderiv ℝ f x (h • basis i + h • basis j) +
        (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i + h • basis j, h • basis i + h • basis j])
  let β : ℝ :=
    f (x + h • basis i) -
      (f x +
        fderiv ℝ f x (h • basis i) +
        (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i, h • basis i])
  let η : ℝ :=
    f (x + h • basis j) -
      (f x +
        fderiv ℝ f x (h • basis j) +
        (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis j, h • basis j])
  have he_norm_i : ‖basis i‖ = 1 := by
    simpa [basis] using (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
  have he_norm_j : ‖basis j‖ = 1 := by
    simpa [basis] using (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one j
  have hstep_norm : ‖h • basis i + h • basis j‖ ≤ 2 * h := by
    -- Bound the mixed step by the sum of the two coordinate steps.
    calc
      ‖h • basis i + h • basis j‖ ≤ ‖h • basis i‖ + ‖h • basis j‖ := norm_add_le _ _
      _ = |h| * ‖basis i‖ + |h| * ‖basis j‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ = h + h := by simp [he_norm_i, he_norm_j, abs_of_pos hh]
      _ = 2 * h := by ring
  have hstep_cube : ‖h • basis i + h • basis j‖ ^ (3 : ℕ) ≤ (2 * h) ^ (3 : ℕ) := by
    -- Monotonicity of the cube turns the norm estimate into the cubic estimate.
    exact pow_le_pow_left₀ (norm_nonneg _) hstep_norm 3
  have h_forward_step_mem_basis :
      ∀ k : Fin n, x + h • basis k ∈ D := by
    intro k
    simpa [basis] using h_forward_step_mem k
  have h_mixed_step_mem_basis :
      ∀ k : Fin n, ∀ l : Fin n, x + h • basis k + h • basis l ∈ D := by
    intro k l
    simpa [basis] using h_mixed_step_mem k l
  have hα :
      |α| ≤ ((4 : ℝ) / 3) * (γ : ℝ) * h ^ (3 : ℕ) := by
    -- Apply the basepoint cubic remainder estimate to the mixed step.
    have hα0 :=
      cubicRemainderBound_of_hessian_basepointLipschitzOn
        (D := D) (f := f) (x := x) (d := h • basis i + h • basis j) (γ := γ)
        hD_open hD_convex hx hf h_hessian_lipschitz
        (show x + (h • basis i + h • basis j) ∈ D by
          simpa [add_assoc] using h_mixed_step_mem_basis i j)
    calc
      |α| ≤ ((γ : ℝ) / 6) * ‖h • basis i + h • basis j‖ ^ (3 : ℕ) := by
        simpa [α, basis]
          using hα0
      _ ≤ ((γ : ℝ) / 6) * (2 * h) ^ (3 : ℕ) := by
        gcongr
      _ = ((4 : ℝ) / 3) * (γ : ℝ) * h ^ (3 : ℕ) := by
        ring
  have hβ :
      |β| ≤ ((γ : ℝ) / 6) * h ^ (3 : ℕ) := by
    -- The single-coordinate remainder is exactly the Chapter 1 cubic estimate with `‖e i‖ = 1`.
    have hβ0 :=
      cubicRemainderBound_of_hessian_basepointLipschitzOn
        (D := D) (f := f) (x := x) (d := h • basis i) (γ := γ)
        hD_open hD_convex hx hf h_hessian_lipschitz (h_forward_step_mem_basis i)
    simpa [β, basis, norm_smul, Real.norm_eq_abs, he_norm_i, abs_of_pos hh, mul_assoc]
      using hβ0
  have hη :
      |η| ≤ ((γ : ℝ) / 6) * h ^ (3 : ℕ) := by
    -- The same estimate handles the `j`-coordinate remainder.
    have hη0 :=
      cubicRemainderBound_of_hessian_basepointLipschitzOn
        (D := D) (f := f) (x := x) (d := h • basis j) (γ := γ)
        hD_open hD_convex hx hf h_hessian_lipschitz (h_forward_step_mem_basis j)
    simpa [η, basis, norm_smul, Real.norm_eq_abs, he_norm_j, abs_of_pos hh, mul_assoc]
      using hη0
  have hsurface :
      (f (x + h • basis i + h • basis j) - f x -
          fderiv ℝ f x (h • basis i + h • basis j) -
          (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i + h • basis j, h • basis i + h • basis j]) -
        (f (x + h • basis i) - f x -
          fderiv ℝ f x (h • basis i) -
          (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i, h • basis i]) -
        (f (x + h • basis j) - f x -
          fderiv ℝ f x (h • basis j) -
          (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis j, h • basis j]) =
      α - β - η := by
    calc
      (f (x + h • basis i + h • basis j) - f x -
            fderiv ℝ f x (h • basis i + h • basis j) -
            (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i + h • basis j, h • basis i + h • basis j]) -
          (f (x + h • basis i) - f x -
            fderiv ℝ f x (h • basis i) -
            (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i, h • basis i]) -
          (f (x + h • basis j) - f x -
            fderiv ℝ f x (h • basis j) -
            (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis j, h • basis j])
          =
            (f (x + (h • basis i + h • basis j)) - f x -
                fderiv ℝ f x (h • basis i + h • basis j) -
                (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i + h • basis j, h • basis i + h • basis j]) -
              (f (x + h • basis i) - f x -
                fderiv ℝ f x (h • basis i) -
                (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i, h • basis i]) -
              (f (x + h • basis j) - f x -
                fderiv ℝ f x (h • basis j) -
                (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis j, h • basis j]) := by
              simp [add_assoc]
      _ = α - β - η := by
        dsimp [α, β, η]
        ring_nf
  have htriangle : |α - β - η| ≤ |α| + |β| + |η| := by
    -- Use the triangle inequality twice to expose the three source remainders separately.
    have hab : |α - β| ≤ |α| + |β| := by
      simpa [sub_eq_add_neg, abs_neg] using (abs_add_le α (-β))
    calc
      |α - β - η| = |(α + (-β)) + (-η)| := by ring_nf
      _ ≤ |α - β| + |η| := by
        simpa [sub_eq_add_neg, abs_neg] using (abs_add_le (α - β) (-η))
      _ ≤ (|α| + |β|) + |η| := by
        gcongr
      _ = |α| + |β| + |η| := by
        ring
  calc
    |(f (x + h • basis i + h • basis j) - f x -
          fderiv ℝ f x (h • basis i + h • basis j) -
          (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i + h • basis j, h • basis i + h • basis j]) -
        (f (x + h • basis i) - f x -
          fderiv ℝ f x (h • basis i) -
          (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i, h • basis i]) -
        (f (x + h • basis j) - f x -
          fderiv ℝ f x (h • basis j) -
          (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis j, h • basis j])|
        = |α - β - η| := by
          rw [hsurface]
    _ ≤ |α| + |β| + |η| := htriangle
    _ ≤ ((4 : ℝ) / 3) * (γ : ℝ) * h ^ (3 : ℕ) +
          (((γ : ℝ) / 6) * h ^ (3 : ℕ) + ((γ : ℝ) / 6) * h ^ (3 : ℕ)) := by
          nlinarith [hα, hβ, hη]
    _ = ((5 : ℝ) / 3) * (γ : ℝ) * h ^ (3 : ℕ) := by
      ring

/-- Helper for Chapter03 Theorem 3.4.3: dividing the scaled inequality by the positive factor
`h²` converts the `h³` estimate into the desired `h` estimate. -/
lemma entry_error_bound_of_hsq_mul_le_hcube
    {h : ℝ}
    (hh : 0 < h)
    {z C : ℝ}
    (hz : |h ^ (2 : ℕ) * z| ≤ C * h ^ (3 : ℕ)) :
    |z| ≤ C * h := by
  have hsqpos : 0 < h ^ (2 : ℕ) := pow_pos hh 2
  have hscaled :
      h ^ (2 : ℕ) * |z| ≤ h ^ (2 : ℕ) * (C * h) := by
    -- Rewrite both sides with the same positive factor `h²`.
    have hz' : h ^ (2 : ℕ) * |z| ≤ C * h ^ (3 : ℕ) := by
      rwa [abs_mul, abs_of_pos hsqpos] at hz
    rwa [show C * h ^ (3 : ℕ) = h ^ (2 : ℕ) * (C * h) by ring] at hz'
  exact le_of_mul_le_mul_left hscaled hsqpos

/-- Helper for Chapter03 Theorem 3.4.3: a uniform entrywise bound controls every row `ℓ₁` norm
by multiplying the entry bound with the dimension. -/
lemma row_oneNorm_le_of_entry_bound
    (E : Hessian) (C : ℝ) (hC : 0 ≤ C)
    (hentry : ∀ i j, |E i j| ≤ C) :
    ∀ i : Fin n, ‖E.row i‖₁ ≤ C * n := by
  intro i
  -- Sum the coordinatewise absolute-value bound across the chosen row.
  calc
    ‖E.row i‖₁ = ∑ j : Fin n, |E i j| := by
      simp [l1Norm_eq_sum_abs, Matrix.row_apply]
    _ ≤ ∑ _j : Fin n, C := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact hentry i j
    _ = (n : ℝ) * C := by
      simp [Finset.card_univ]
    _ = C * n := by ring

/-- Chapter03 Theorem 3.4.3 (1): under the Chapter03 Theorem 3.4.2 hypotheses, if `h > 0`,
`x + h • e_i ∈ D` for every coordinate direction, and every mixed forward point
`x + h • e_i + h • e_j` also lies in `D`, then the forward mixed-difference entry
`finiteDifferenceHessianMatrix f x h i j` approximates the coordinate Hessian entry
`hessianMatrixAt f x i j` with error at most `((5 : ℝ) / 3) * γ * h`. -/
theorem finiteDifferenceHessianMatrix_entry_error_bound
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (h : ℝ) (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hf : ContDiffOn ℝ 2 f D)
    (h_hessian_lipschitz :
      ∀ y ∈ D,
        ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ (γ : ℝ) * ‖y - x‖)
    (hh : 0 < h)
    (h_forward_step_mem :
      ∀ i : Fin n, x + h • EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (h_mixed_step_mem :
      ∀ i : Fin n, ∀ j : Fin n,
        x + h • EuclideanSpace.basisFun (Fin n) ℝ i +
          h • EuclideanSpace.basisFun (Fin n) ℝ j ∈ D)
    (i j : Fin n) :
    |finiteDifferenceHessianMatrix f x h i j - hessianMatrixAt f x i j| ≤
      ((5 : ℝ) / 3) * (γ : ℝ) * h := by
  let basis : Fin n → EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ
  let α : ℝ :=
    f (x + h • basis i + h • basis j) - f x -
      fderiv ℝ f x (h • basis i + h • basis j) -
      (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i + h • basis j, h • basis i + h • basis j]
  let β : ℝ :=
    f (x + h • basis i) - f x -
      fderiv ℝ f x (h • basis i) -
      (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis i, h • basis i]
  let η : ℝ :=
    f (x + h • basis j) - f x -
      fderiv ℝ f x (h • basis j) -
      (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![h • basis j, h • basis j]
  have hC2x : ContDiffAt ℝ 2 f x := hf.contDiffAt (hD_open.mem_nhds hx)
  have hscaled :
      h ^ (2 : ℕ) * (finiteDifferenceHessianMatrix f x h i j - hessianMatrixAt f x i j) =
        α - β - η := by
    -- This is the source identity `(3.4.16)` from the alpha-beta-eta decomposition.
    simpa [α, β, η, basis] using
      finiteDifferenceHessian_scaled_entry_error_eq_alpha_sub_beta_sub_eta
        (D := D) (f := f) (x := x) (h := h) (γ := γ)
        hD_open hD_convex hx hf h_hessian_lipschitz hh h_forward_step_mem
        hC2x h_mixed_step_mem i j
  have hscaled_bound :
      |h ^ (2 : ℕ) * (finiteDifferenceHessianMatrix f x h i j - hessianMatrixAt f x i j)| ≤
        ((5 : ℝ) / 3) * (γ : ℝ) * h ^ (3 : ℕ) := by
    -- Package the three Taylor remainders into the textbook `5γh³/3` estimate.
    rw [hscaled]
    simpa [α, β, η, basis] using
      finiteDifferenceHessian_alpha_beta_eta_combined_bound
        (D := D) (f := f) (x := x) (h := h) (γ := γ)
        hD_open hD_convex hx hf h_hessian_lipschitz hh h_forward_step_mem
        h_mixed_step_mem i j
  -- Divide the scaled estimate by `h²` to recover the entrywise error bound.
  exact
    entry_error_bound_of_hsq_mul_le_hcube
      (h := h) (hh := hh)
      (z := finiteDifferenceHessianMatrix f x h i j - hessianMatrixAt f x i j)
      (C := ((5 : ℝ) / 3) * (γ : ℝ))
      hscaled_bound

/-- Helper for Chapter03 Theorem 3.4.3: every row `ℓ₁` norm of the Hessian approximation error is
bounded by the pointwise error constant times the dimension. -/
lemma finiteDifferenceHessianError_row_oneNorm_le
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (h : ℝ) (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hf : ContDiffOn ℝ 2 f D)
    (h_hessian_lipschitz :
      ∀ y ∈ D,
        ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ (γ : ℝ) * ‖y - x‖)
    (hh : 0 < h)
    (h_forward_step_mem :
      ∀ i : Fin n, x + h • EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (h_mixed_step_mem :
      ∀ i : Fin n, ∀ j : Fin n,
        x + h • EuclideanSpace.basisFun (Fin n) ℝ i +
          h • EuclideanSpace.basisFun (Fin n) ℝ j ∈ D) :
    ∀ i : Fin n,
      ‖(finiteDifferenceHessianMatrix f x h - hessianMatrixAt f x).row i‖₁ ≤
        (((5 : ℝ) / 3) * (γ : ℝ) * h) * n := by
  have hC : 0 ≤ ((5 : ℝ) / 3) * (γ : ℝ) * h := by positivity
  -- Package the entrywise bound row by row using the general row-sum helper.
  exact
    row_oneNorm_le_of_entry_bound
      (E := finiteDifferenceHessianMatrix f x h - hessianMatrixAt f x)
      (((5 : ℝ) / 3) * (γ : ℝ) * h) hC
      (fun i j ↦ by
        simpa [sub_eq_add_neg] using
          finiteDifferenceHessianMatrix_entry_error_bound
            (D := D) (f := f) (x := x) (h := h) (γ := γ)
            hD_open hD_convex hx hf h_hessian_lipschitz hh h_forward_step_mem
            h_mixed_step_mem i j)

/-- Helper for Chapter03 Theorem 3.4.3: the max-entry norm of the Hessian approximation error is
bounded by the pointwise entry estimate. -/
lemma finiteDifferenceHessianError_maxEntryNorm_le
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (h : ℝ) (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hf : ContDiffOn ℝ 2 f D)
    (h_hessian_lipschitz :
      ∀ y ∈ D,
        ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ (γ : ℝ) * ‖y - x‖)
    (hh : 0 < h)
    (h_forward_step_mem :
      ∀ i : Fin n, x + h • EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (h_mixed_step_mem :
      ∀ i : Fin n, ∀ j : Fin n,
        x + h • EuclideanSpace.basisFun (Fin n) ℝ i +
          h • EuclideanSpace.basisFun (Fin n) ℝ j ∈ D) :
    matrixMaxEntryNorm (finiteDifferenceHessianMatrix f x h - hessianMatrixAt f x) ≤
      ((5 : ℝ) / 3) * (γ : ℝ) * h := by
  have hC : 0 ≤ ((5 : ℝ) / 3) * (γ : ℝ) * h := by positivity
  -- The elementwise matrix norm is controlled coordinatewise by the entry estimate.
  unfold matrixMaxEntryNorm
  refine (Matrix.norm_le_iff hC).2 ?_
  intro i j
  simpa [Real.norm_eq_abs, sub_eq_add_neg] using
    finiteDifferenceHessianMatrix_entry_error_bound
      (D := D) (f := f) (x := x) (h := h) (γ := γ)
      hD_open hD_convex hx hf h_hessian_lipschitz hh h_forward_step_mem
      h_mixed_step_mem i j

/-- Chapter03 Theorem 3.4.3 (2): under the same hypotheses as `(1)`, the matrix `ℓ₁` norm of the
forward mixed-difference Hessian error is bounded by `((5 : ℝ) / 3) * γ * h * n`. -/
theorem matrixOneNorm_finiteDifferenceHessianError_le
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (h : ℝ) (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hf : ContDiffOn ℝ 2 f D)
    (h_hessian_lipschitz :
      ∀ y ∈ D,
        ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ (γ : ℝ) * ‖y - x‖)
    (hh : 0 < h)
    (h_forward_step_mem :
      ∀ i : Fin n, x + h • EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (h_mixed_step_mem :
      ∀ i : Fin n, ∀ j : Fin n,
        x + h • EuclideanSpace.basisFun (Fin n) ℝ i +
          h • EuclideanSpace.basisFun (Fin n) ℝ j ∈ D)
    :
    ‖finiteDifferenceHessianMatrix f x h - hessianMatrixAt f x‖₁ ≤
      ((5 : ℝ) / 3) * (γ : ℝ) * h * n := by
  let E : Matrix (Fin n) (Fin n) ℝ := finiteDifferenceHessianMatrix f x h - hessianMatrixAt f x
  have hC : 0 ≤ ((5 : ℝ) / 3) * (γ : ℝ) * h := by positivity
  have hrow :
      ∀ i : Fin n, ‖(E.transpose).row i‖₁ ≤ (((5 : ℝ) / 3) * (γ : ℝ) * h) * n := by
    -- Apply the general row-sum bound to the transpose using the transposed entry estimate.
    refine row_oneNorm_le_of_entry_bound
      (E := E.transpose) (((5 : ℝ) / 3) * (γ : ℝ) * h) hC ?_
    intro i j
    simpa [E, Matrix.transpose_apply, sub_eq_add_neg] using
      finiteDifferenceHessianMatrix_entry_error_bound
        (D := D) (f := f) (x := x) (h := h) (γ := γ)
        hD_open hD_convex hx hf h_hessian_lipschitz hh h_forward_step_mem
        h_mixed_step_mem j i
  -- Transport the transpose row bounds through the Chapter 1 `ℓ₁`-to-`ℓ∞` bridge.
  rw [matrixOneNorm_eq_matrixInfinityNorm_transpose]
  exact
    matrixInfinityNorm_le_of_rowVectorOneNorm_le E.transpose
      ((((5 : ℝ) / 3) * (γ : ℝ) * h) * n) (by positivity) hrow

/-- Chapter03 Theorem 3.4.3 (3): under the same hypotheses as `(1)`, the matrix `ℓ∞` norm of the
forward mixed-difference Hessian error is bounded by `((5 : ℝ) / 3) * γ * h * n`. -/
theorem matrixInfinityNorm_finiteDifferenceHessianError_le
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (h : ℝ) (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hf : ContDiffOn ℝ 2 f D)
    (h_hessian_lipschitz :
      ∀ y ∈ D,
        ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ (γ : ℝ) * ‖y - x‖)
    (hh : 0 < h)
    (h_forward_step_mem :
      ∀ i : Fin n, x + h • EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (h_mixed_step_mem :
      ∀ i : Fin n, ∀ j : Fin n,
        x + h • EuclideanSpace.basisFun (Fin n) ℝ i +
          h • EuclideanSpace.basisFun (Fin n) ℝ j ∈ D)
    :
    ‖finiteDifferenceHessianMatrix f x h - hessianMatrixAt f x‖∞ ≤
      ((5 : ℝ) / 3) * (γ : ℝ) * h * n := by
  -- Package the rowwise `ℓ₁` bound through the Chapter 1 `ℓ∞` owner API.
  exact
    matrixInfinityNorm_le_of_rowVectorOneNorm_le
      (finiteDifferenceHessianMatrix f x h - hessianMatrixAt f x)
      ((((5 : ℝ) / 3) * (γ : ℝ) * h) * n) (by positivity)
      (finiteDifferenceHessianError_row_oneNorm_le
        (D := D) (f := f) (x := x) (h := h) (γ := γ)
        hD_open hD_convex hx hf h_hessian_lipschitz hh h_forward_step_mem
        h_mixed_step_mem)

/-- Chapter03 Theorem 3.4.3 (4): under the same hypotheses as `(1)`, the Frobenius norm of the
forward mixed-difference Hessian error is bounded by `((5 : ℝ) / 3) * γ * h * n`. -/
theorem matrixFrobeniusNorm_finiteDifferenceHessianError_le
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (h : ℝ) (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hf : ContDiffOn ℝ 2 f D)
    (h_hessian_lipschitz :
      ∀ y ∈ D,
        ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ (γ : ℝ) * ‖y - x‖)
    (hh : 0 < h)
    (h_forward_step_mem :
      ∀ i : Fin n, x + h • EuclideanSpace.basisFun (Fin n) ℝ i ∈ D)
    (h_mixed_step_mem :
      ∀ i : Fin n, ∀ j : Fin n,
        x + h • EuclideanSpace.basisFun (Fin n) ℝ i +
          h • EuclideanSpace.basisFun (Fin n) ℝ j ∈ D)
    :
    ‖finiteDifferenceHessianMatrix f x h - hessianMatrixAt f x‖_F ≤
      ((5 : ℝ) / 3) * (γ : ℝ) * h * n := by
  let E : Matrix (Fin n) (Fin n) ℝ := finiteDifferenceHessianMatrix f x h - hessianMatrixAt f x
  have hsqrtnsq : Real.sqrt ((n * n : ℕ) : ℝ) = (n : ℝ) := by
    -- Rewrite `sqrt (n^2)` to `n` on the nonnegative real line.
    have hcast : (((n * n : ℕ) : ℝ)) = (n : ℝ) ^ (2 : ℕ) := by
      exact_mod_cast (show n * n = n ^ (2 : ℕ) by rw [pow_two])
    rw [hcast]
    simp [Real.sqrt_sq_eq_abs, abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
  calc
    ‖E‖_F ≤ Real.sqrt ((n * n : ℕ) : ℝ) * matrixMaxEntryNorm E :=
      matrixFrobeniusNorm_le_sqrt_mul_matrixMaxEntryNorm E
    _ ≤ Real.sqrt ((n * n : ℕ) : ℝ) * (((5 : ℝ) / 3) * (γ : ℝ) * h) := by
      gcongr
      exact finiteDifferenceHessianError_maxEntryNorm_le
        (D := D) (f := f) (x := x) (h := h) (γ := γ)
        hD_open hD_convex hx hf h_hessian_lipschitz hh h_forward_step_mem
        h_mixed_step_mem
    _ = ((5 : ℝ) / 3) * (γ : ℝ) * h * n := by
      rw [hsqrtnsq]
      ring

end Theorem343
