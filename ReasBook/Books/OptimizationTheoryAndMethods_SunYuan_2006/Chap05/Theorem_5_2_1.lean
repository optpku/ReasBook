/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1

noncomputable section

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this file:
-- * primary domain: exact-line-search Broyden-class quasi-Newton runs on Euclidean quadratic
--   objectives;
-- * sampled project owners in the minimal closure:
--   `GeneralQuasiNewtonMethod`,
--   `GeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay`,
--   `quadraticObjective`,
--   `broydenStep` / `broydenSecant`,
--   `broydenClassInverseUpdate`;
-- * core/canonical owner reused for exact line search: `A.HasExactLineSearchOnNonnegativeRay`;
-- * source-facing owner for the Broyden update data:
--   `GeneralQuasiNewtonMethod.IsBroydenClassRun`;
-- * source-facing specialization for Theorem 5.2.1:
--   `GeneralQuasiNewtonMethod.IsBroydenClassMethod`;
-- * primitive data: a quasi-Newton run together with the secant denominators and Broyden
--   inverse-update data at each nonterminal stage, reusing the upstream exact-line-search owner;
-- * derived API: `GeneralQuasiNewtonMethod.GeneratedThrough`, the stagewise `stepSpec`, and the
--   five quadratic-termination theorems below.

namespace GeneralQuasiNewtonMethod

section BroydenClassRun

variable {f : Point → ℝ}

/-- An exact-line-search Broyden-class run for `f` is a general quasi-Newton run with zero
stopping tolerance and, at every nonterminal stage, the ordinary secant denominators and the
explicit inverse-Hessian Broyden-class update on the Euclidean matrix model `A.matrix`,
reusing the Chapter 5 exact-line-search owner `A.HasExactLineSearchOnNonnegativeRay`. -/
structure IsBroydenClassRun
    (A : GeneralQuasiNewtonMethod f) (φ : ℕ → ℝ) : Prop
    extends A.HasExactLineSearchOnNonnegativeRay where
  epsilon_eq_zero : A.ε = 0
  secant_dot_ne_zero (k : ℕ) (hk : A.ε < ‖A.g k‖) :
    dotProduct (broydenStep A k) (broydenSecant A.g k) ≠ 0
  curvature_dot_ne_zero (k : ℕ) (hk : A.ε < ‖A.g k‖) :
    dotProduct (broydenSecant A.g k) ((A.matrix k).mulVec (broydenSecant A.g k)) ≠ 0
  update_eq (k : ℕ) (hk : A.ε < ‖A.g k‖) :
    A.matrix (k + 1) =
      broydenClassInverseUpdate (A.matrix k) (broydenStep A k) (broydenSecant A.g k) (φ k)

namespace IsBroydenClassRun

/-- Every nonterminal Broyden-class stage has exact line search, admissible secant
denominators, and the explicit inverse-Hessian Broyden update formula. -/
theorem stepSpec
    {A : GeneralQuasiNewtonMethod f} {φ : ℕ → ℝ}
    (hBroyden : A.IsBroydenClassRun φ) {k : ℕ}
    (hk : A.ε < ‖A.g k‖) :
    IsMinOn (lineSearchObjective f (A k) (A.d k)) (Set.Ici 0) (A.α k) ∧
      dotProduct (broydenStep A k) (broydenSecant A.g k) ≠ 0 ∧
      dotProduct (broydenSecant A.g k) ((A.matrix k).mulVec (broydenSecant A.g k)) ≠ 0 ∧
      A.matrix (k + 1) =
        broydenClassInverseUpdate (A.matrix k) (broydenStep A k) (broydenSecant A.g k) (φ k) :=
  ⟨hBroyden.toHasExactLineSearchOnNonnegativeRay.isMinOn k, hBroyden.secant_dot_ne_zero k hk,
    hBroyden.curvature_dot_ne_zero k hk, hBroyden.update_eq k hk⟩

end IsBroydenClassRun

end BroydenClassRun

section BroydenClassMethod

variable {G : MatrixN} {b : Point} {c : ℝ}

local notation "f" => quadraticObjective G b c

/-- A Broyden-class method for the quadratic objective `quadraticObjective G b c` is an
exact-line-search Broyden-class run for that objective together with the positive-definite
quadratic Hessian `G`. -/
structure IsBroydenClassMethod
    (A : GeneralQuasiNewtonMethod f) (φ : ℕ → ℝ) : Prop where
  toIsBroydenClassRun : A.IsBroydenClassRun φ
  posDef : G.PosDef

namespace IsBroydenClassMethod

/-- A nonterminal quadratic Broyden-class step has exact line search, admissible secant
denominators, and the explicit Broyden-class inverse update formula. -/
theorem stepSpec
    {A : GeneralQuasiNewtonMethod f} {φ : ℕ → ℝ}
    (hBroyden : A.IsBroydenClassMethod φ) {k : ℕ}
    (hk : A.ε < ‖A.g k‖) :
    IsMinOn (lineSearchObjective f (A k) (A.d k)) (Set.Ici 0) (A.α k) ∧
      dotProduct (broydenStep A k) (broydenSecant A.g k) ≠ 0 ∧
      dotProduct (broydenSecant A.g k) ((A.matrix k).mulVec (broydenSecant A.g k)) ≠ 0 ∧
      A.matrix (k + 1) =
        broydenClassInverseUpdate (A.matrix k) (broydenStep A k) (broydenSecant A.g k) (φ k) :=
  hBroyden.toIsBroydenClassRun.stepSpec hk

/-- The predicate `IsBroydenClassMethod` is proof-irrelevant. -/
instance isBroydenClassMethod_subsingleton
    {A : GeneralQuasiNewtonMethod f} {φ : ℕ → ℝ} :
    Subsingleton (A.IsBroydenClassMethod φ) := inferInstance

end IsBroydenClassMethod

/-- Chapter05 Theorem 5.2.1 (1): for a positive-definite quadratic objective and an exact
line-search Broyden-class run, the hereditary property holds along every generated stage up to
`m`, namely `H (i + 1) y j = s j` for all `j ≤ i ≤ m`. -/
theorem broydenClassMethod_hereditary
    (A : GeneralQuasiNewtonMethod f)
    (φ : ℕ → ℝ)
    (hBroyden : A.IsBroydenClassMethod φ) {m : ℕ}
    (hGenerated : A.GeneratedThrough (m + 1)) :
    ∀ ⦃i j : ℕ⦄, i ≤ m → j ≤ i →
      (A.matrix (i + 1)).mulVec (broydenSecant A.g j) = broydenStep A j := sorry

/-- Chapter05 Theorem 5.2.1 (2): for a positive-definite quadratic objective and an exact
line-search Broyden-class run, the generated steps are pairwise `G`-conjugate up to `m`,
namely `s iᵀ G s j = 0` whenever `j < i ≤ m`. -/
theorem broydenClassMethod_conjugateDirections
    (A : GeneralQuasiNewtonMethod f)
    (φ : ℕ → ℝ)
    (hBroyden : A.IsBroydenClassMethod φ) {m : ℕ}
    (hGenerated : A.GeneratedThrough (m + 1)) :
    ∀ ⦃i j : ℕ⦄, i ≤ m → j < i →
      dotProduct (broydenStep A i) (G.mulVec (broydenStep A j)) = 0 := sorry

/-- Chapter05 Theorem 5.2.1 (3): an exact line-search Broyden-class run on a quadratic
objective with positive-definite Hessian `G` terminates after some stages `0, ..., m`, with
termination at stage `m + 1`. -/
theorem broydenClassMethod_quadraticTermination
    (A : GeneralQuasiNewtonMethod f)
    (φ : ℕ → ℝ)
    (hBroyden : A.IsBroydenClassMethod φ) :
    ∃ m : ℕ, A.GeneratedThrough (m + 1) ∧
      A.terminatedAt (m + 1) := sorry

/-- Chapter05 Theorem 5.2.1 (4): if the exact line-search Broyden-class run on a quadratic
objective with positive-definite Hessian `G` is generated through stage `m` and terminates at
stage `m + 1`, then the termination index satisfies the book's bound `m + 1 ≤ n`. -/
theorem broydenClassMethod_terminationBound
    (A : GeneralQuasiNewtonMethod f)
    (φ : ℕ → ℝ)
    (hBroyden : A.IsBroydenClassMethod φ)
    {m : ℕ}
    (hGenerated : A.GeneratedThrough (m + 1))
    (hTerm : A.terminatedAt (m + 1)) :
    m + 1 ≤ n := sorry

/-- Chapter05 Theorem 5.2.1 (5): if the exact line-search Broyden-class run on a quadratic
objective with positive-definite Hessian `G` remains nonterminal through the first `n`
directions and terminates at stage `n`, then `A.matrix n = G⁻¹`. -/
theorem broydenClassMethod_finalInverse
    (A : GeneralQuasiNewtonMethod f)
    (φ : ℕ → ℝ)
    (hBroyden : A.IsBroydenClassMethod φ)
    (hGenerated : A.GeneratedThrough n)
    (hTerm : A.terminatedAt n) :
    A.matrix n = G⁻¹ := sorry

end BroydenClassMethod

end GeneralQuasiNewtonMethod

end
