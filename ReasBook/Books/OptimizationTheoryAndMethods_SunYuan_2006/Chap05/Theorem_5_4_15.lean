/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Lemma_5_4_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9

noncomputable section

section Chapter05Theorem5415

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * primary domain: local DFP convergence for Hessian-side quasi-Newton iterations;
-- * owner declarations reused here: `DFPHessianRun`,
--   `dfpReferenceHessian`, `dfpMatrixNorm`, and
--   `dfpOneThirdConditionInNeighborhood` from
--   `Lemma_5_4_19`, together with the canonical Chapter 5 rate owner `LinearlyConvergesTo`
--   from `Theorem_5_4_9`;
-- * layer choice: this file is source-facing for the DFP small-start conclusion, while the DFP
--   run data and auxiliary local-start quantities are reused from the earlier owner files;
-- * primitive data: the source-facing Hessian-side run owner is `DFPHessianRun D f`, and the
--   prescribed initial data are imposed by the equalities `A.x0 = x0` and `A.B0 = B0`;
-- * derived API in this file is only the small-start linear-convergence statement over that
--   owner.

/-- Chapter05 Theorem 5.4.15: let `f : ℝ^n → ℝ` satisfy
`HasQuasiNewtonStrongLocalMinimizerAssumptions D f`. Assume the neighborhood one-third
condition `dfpOneThirdConditionInNeighborhood h`, namely `(5.4.83)` with
`μ = ‖(∇²f(h.xStar))⁻¹‖` and `σ(x, xNext) = max {‖x - h.xStar‖, ‖xNext - h.xStar‖}`.
Then there exist `ε > 0` and `δ > 0` such that every initial pair `(x0, B0)` with
`‖x0 - h.xStar‖ < ε` and
`dfpMatrixNorm (dfpReferenceHessian h) (B0 - dfpReferenceHessian h) < δ`
admits a well-defined DFP iteration `(5.4.79)`-`(5.4.80)` on `D`, and the produced iterate
sequence converges linearly to `h.xStar`. The small-start conclusion is packaged into the
reusable owner `DFPSmallStartConvergence`. -/
class DFPSmallStartConvergence
    (D : Set Point) (f : Point → ℝ) (xStar : outParam Point) (x0 : Point) (B0 : MatrixN) :
    Prop where
  exists_run :
    ∃ A : DFPHessianRun D f, A.x0 = x0 ∧ A.B0 = B0 ∧ LinearlyConvergesTo A xStar
  linear :
    ∀ A : DFPHessianRun D f, A.x0 = x0 → A.B0 = B0 → LinearlyConvergesTo A xStar

namespace DFPSmallStartConvergence

instance instNonemptyRun
    {D : Set Point} {f : Point → ℝ} {xStar x0 : Point} {B0 : MatrixN}
    [h : DFPSmallStartConvergence D f xStar x0 B0] :
    Nonempty {A : DFPHessianRun D f // A.x0 = x0 ∧ A.B0 = B0} := by
  rcases h.exists_run with ⟨A, hx0, hB0, _⟩
  exact ⟨⟨A, hx0, hB0⟩⟩

theorem nonempty_run
    {D : Set Point} {f : Point → ℝ} {xStar x0 : Point} {B0 : MatrixN}
    (h : DFPSmallStartConvergence D f xStar x0 B0) :
    Nonempty {A : DFPHessianRun D f // A.x0 = x0 ∧ A.B0 = B0} := by
  letI := h
  infer_instance

theorem to_exists_and_forall
    {D : Set Point} {f : Point → ℝ} {xStar x0 : Point} {B0 : MatrixN}
    (h : DFPSmallStartConvergence D f xStar x0 B0) :
    (∃ A : DFPHessianRun D f, A.x0 = x0 ∧ A.B0 = B0 ∧ LinearlyConvergesTo A xStar) ∧
      ∀ A : DFPHessianRun D f, A.x0 = x0 → A.B0 = B0 → LinearlyConvergesTo A xStar := by
  exact ⟨h.exists_run, h.linear⟩

end DFPSmallStartConvergence

/-- Chapter05 Theorem 5.4.15: under the neighborhood one-third condition from `(5.4.83)`,
small initial DFP errors produce the canonical small-start owner
`DFPSmallStartConvergence D f h.xStar x0 B0`. -/
theorem dfpMethod_linearlyConvergesTo_of_small_initial_errors
    (D : Set Point) (f : Point → ℝ)
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f)
    (h_oneThird : dfpOneThirdConditionInNeighborhood h) :
    ∃ ε > 0, ∃ δ > 0, ∀ x0 B0,
      ‖x0 - h.xStar‖ < ε →
      dfpMatrixNorm (dfpReferenceHessian h) (B0 - dfpReferenceHessian h) < δ →
      DFPSmallStartConvergence D f h.xStar x0 B0 := sorry

end Chapter05Theorem5415
