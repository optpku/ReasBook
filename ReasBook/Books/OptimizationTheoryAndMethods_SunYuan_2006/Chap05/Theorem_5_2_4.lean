/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_3_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_2_1

noncomputable section

open Matrix
open GeneralQuasiNewtonMethod

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this file:
-- * primary domain: exact-line-search Broyden-class quasi-Newton runs on `ℝ^n`;
-- * sampled Chapter 5 owners: `GeneralQuasiNewtonMethod.IsBroydenClassRun` from `Theorem_5_2_1`,
--   `GeneralQuasiNewtonMethod` from `Algorithm_5_1_1`, `bfgsInverseUpdate` from
--   `Definition_5_1_extra_4`, and `broydenClassMu` from `Definition_5_2_extra_1`;
-- * core/canonical owner abstraction:
--   `A.IsBroydenClassRun φ` from `Theorem_5_2_1`;
-- * source-facing layer here: the common assumption bundle
--   `ParameterIndependenceAssumptions A A' φ φ'` together with the two
--   parameter-independence conclusions for Broyden-class runs;
-- * primitive data added here beyond the upstream owner: the stagewise positive secant
--   curvature and the parameter lower bound `(5.2.20)`;
-- * derived API:
--   `GeneralQuasiNewtonMethod.GeneratedThrough` and the tail-agreement hypothesis
--   `Set.EqOn φ φ' (Set.Ici k)` used in the theorem statements.

section BroydenClassParameterIndependence

variable {f : Point → ℝ}

/-- Chapter05 Theorem 5.2.4 common assumptions: `f` is `C¹`, the level set
`quasiNewtonLevelSet f A.x₀` is bounded, both sequences are exact-line-search Broyden-class
runs satisfying the stagewise positive secant-curvature and parameter lower-bound hypotheses,
the initial iterates agree, the initial inverse matrices agree, and the common initial matrix
is positive definite. -/
def ParameterIndependenceAssumptions
    (A A' : GeneralQuasiNewtonMethod f) (φ φ' : ℕ → ℝ) : Prop :=
  A.IsBroydenClassRun φ ∧
    (∀ k : ℕ, A.ε < ‖A.g k‖ →
      0 < dotProduct (broydenStep A k) (broydenSecant A.g k)) ∧
    (∀ k : ℕ, A.ε < ‖A.g k‖ →
      1 /
            (1 -
              broydenClassMu
                (A.matrix k) ((A.matrix k)⁻¹) (broydenStep A k) (broydenSecant A.g k)) <
        φ k) ∧
    A'.IsBroydenClassRun φ' ∧
    (∀ k : ℕ, A'.ε < ‖A'.g k‖ →
      0 < dotProduct (broydenStep A' k) (broydenSecant A'.g k)) ∧
    (∀ k : ℕ, A'.ε < ‖A'.g k‖ →
      1 /
            (1 -
              broydenClassMu
                (A'.matrix k) ((A'.matrix k)⁻¹) (broydenStep A' k) (broydenSecant A'.g k)) <
        φ' k) ∧
    ContDiff ℝ 1 f ∧
    Bornology.IsBounded (quasiNewtonLevelSet f A.x0) ∧
    A'.x0 = A.x0 ∧
    A'.matrix0 = A.matrix0 ∧
    A.matrix0.PosDef

namespace ParameterIndependenceAssumptions

variable {A A' : GeneralQuasiNewtonMethod f} {φ φ' : ℕ → ℝ}

/-- The common bounded level-set hypothesis may be read at the primed initial point because the
initial iterates agree. -/
theorem boundedLevelSet'
    (h : ParameterIndependenceAssumptions A A' φ φ') :
    Bornology.IsBounded (quasiNewtonLevelSet f A'.x0) :=
  match (show
      A.IsBroydenClassRun φ ∧
        (∀ k : ℕ, A.ε < ‖A.g k‖ →
          0 < dotProduct (broydenStep A k) (broydenSecant A.g k)) ∧
        (∀ k : ℕ, A.ε < ‖A.g k‖ →
          1 /
                (1 -
                  broydenClassMu
                    (A.matrix k) ((A.matrix k)⁻¹) (broydenStep A k) (broydenSecant A.g k)) <
            φ k) ∧
        A'.IsBroydenClassRun φ' ∧
        (∀ k : ℕ, A'.ε < ‖A'.g k‖ →
          0 < dotProduct (broydenStep A' k) (broydenSecant A'.g k)) ∧
        (∀ k : ℕ, A'.ε < ‖A'.g k‖ →
          1 /
                (1 -
                  broydenClassMu
                    (A'.matrix k) ((A'.matrix k)⁻¹) (broydenStep A' k) (broydenSecant A'.g k)) <
            φ' k) ∧
        ContDiff ℝ 1 f ∧
        Bornology.IsBounded (quasiNewtonLevelSet f A.x0) ∧
        A'.x0 = A.x0 ∧
        A'.matrix0 = A.matrix0 ∧
        A.matrix0.PosDef from h) with
  | ⟨_, _, _, _, _, _, _, hBoundedLevelSet, hx0_eq, _, _⟩ => hx0_eq ▸ hBoundedLevelSet

/-- The common positive-definite initial matrix may be read on the primed run because the
initial inverse-approximation matrices agree. -/
theorem matrix0_posDef'
    (h : ParameterIndependenceAssumptions A A' φ φ') :
    A'.matrix0.PosDef :=
  match (show
      A.IsBroydenClassRun φ ∧
        (∀ k : ℕ, A.ε < ‖A.g k‖ →
          0 < dotProduct (broydenStep A k) (broydenSecant A.g k)) ∧
        (∀ k : ℕ, A.ε < ‖A.g k‖ →
          1 /
                (1 -
                  broydenClassMu
                    (A.matrix k) ((A.matrix k)⁻¹) (broydenStep A k) (broydenSecant A.g k)) <
            φ k) ∧
        A'.IsBroydenClassRun φ' ∧
        (∀ k : ℕ, A'.ε < ‖A'.g k‖ →
          0 < dotProduct (broydenStep A' k) (broydenSecant A'.g k)) ∧
        (∀ k : ℕ, A'.ε < ‖A'.g k‖ →
          1 /
                (1 -
                  broydenClassMu
                    (A'.matrix k) ((A'.matrix k)⁻¹) (broydenStep A' k) (broydenSecant A'.g k)) <
            φ' k) ∧
        ContDiff ℝ 1 f ∧
        Bornology.IsBounded (quasiNewtonLevelSet f A.x0) ∧
        A'.x0 = A.x0 ∧
        A'.matrix0 = A.matrix0 ∧
        A.matrix0.PosDef from h) with
  | ⟨_, _, _, _, _, _, _, _, _, hMatrix0_eq, hMatrix0_posDef⟩ => hMatrix0_eq ▸ hMatrix0_posDef

end ParameterIndependenceAssumptions

variable {A A' : GeneralQuasiNewtonMethod f} {φ φ' : ℕ → ℝ}

/-- Chapter05 Theorem 5.2.4 (1): let `f : ℝ^n → ℝ` be continuously differentiable, suppose the
level set `quasiNewtonLevelSet f A.x₀` is bounded, let the common initial matrix `H₀` be
symmetric positive definite, noting that symmetry is already implied by positive definiteness,
and suppose both exact-line-search Broyden-class runs are generated through stage `k + 1`.
If the parameter tails agree on `Set.Ici k`, so `A'` is obtained from `A` by altering only the
earlier parameters `φ₀, ..., φₖ₋₁`, then the next iterate `xₖ₊₁` is independent
of those earlier parameters. -/
theorem broydenClassIterate_independent_of_parameters
    (h : ParameterIndependenceAssumptions A A' φ φ')
    (k : ℕ)
    (hEq : Set.EqOn φ φ' (Set.Ici k))
    (hGenerated : A.GeneratedThrough (k + 1))
    (hGenerated' : A'.GeneratedThrough (k + 1)) :
    A (k + 1) = A' (k + 1) := sorry

/-- Chapter05 Theorem 5.2.4 (2): under the same assumptions as Part (1), for every `k ≥ 0`,
if both runs are generated through stage `k + 1` and the parameter tails agree on `Set.Ici k`,
so `A'` is obtained from `A` by altering only the earlier Broyden parameters
`φ₀, ..., φₖ₋₁`, then the stage-`k` canonical inverse-BFGS update built from the
run data is independent of those earlier parameters. -/
theorem broydenClassBfgsMatrix_independent_of_parameters
    (h : ParameterIndependenceAssumptions A A' φ φ')
    (k : ℕ)
    (hEq : Set.EqOn φ φ' (Set.Ici k))
    (hGenerated : A.GeneratedThrough (k + 1))
    (hGenerated' : A'.GeneratedThrough (k + 1)) :
    bfgsInverseUpdate (A.matrix k) (broydenStep A k) (broydenSecant A.g k) =
      bfgsInverseUpdate (A'.matrix k) (broydenStep A' k) (broydenSecant A'.g k) := sorry

end BroydenClassParameterIndependence

end
