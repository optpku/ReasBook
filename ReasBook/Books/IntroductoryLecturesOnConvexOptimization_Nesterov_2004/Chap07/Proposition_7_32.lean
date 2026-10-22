/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open EuclideanSpace (nonnegativeOrthant)

noncomputable section

universe u

variable {m : ℕ} {OD : Type u} [Fintype OD]

local notation "E" => EuclideanSpace ℝ (Fin m)

/- Proposition 7.32 lies in the Chapter 7 fractional-covering / concurrent-flow duality domain.

Sampled owner-style declarations:
- `fractionalCoveringPhiStar` in `Proposition_7_31`, the source-facing owner of the infimum
  `φ⋆ = inf ⟪b, t⟫ / ψ(t)` on the nonnegative orthant;
- `fractionalCoveringNormalizedPsiSup` in `Proposition_7_31`, the source-facing owner of the
  normalized supremum of `ψ`;
- `fractionalCoveringPhiStar_eq_inv_normalizedPsiSup` in `Proposition_7_31`, the Chapter 7 owner
  theorem that already proves the reciprocal relation used here;
- `IsPositivelyHomogeneousOn` in `Chap03/Definition_3_1_7`, the project owner of positive
  homogeneity on a cone.

Best owner abstraction:
- source-facing: the maximal concurrent-flow dual specialization of Proposition 7.31;
- core/canonical: `fractionalCoveringPhiStar`, `fractionalCoveringNormalizedPsiSup`, and
  `fractionalCoveringPhiStar_eq_inv_normalizedPsiSup`;
- bridge/view: the finite weighted-sum objective `t ↦ ∑ od, d od * shortestPath od t`.

Primitive data:
- the capacity vector `barf`;
- the demand family `d`;
- the shortest-path family `shortestPath`.

Derived API:
- the dual objective written directly as the finite sum over `OD`;
- the reciprocal-value identity below, obtained by specializing the owner theorem.

This refinement deletes the duplicate local wrapper
`maximalConcurrentFlowDualObjective`. That definition was an exact one-file alias for the finite
sum objective and had no downstream users, so the public surface is cleaner if Proposition 7.32
specializes the Chapter 7 owner theorem directly to the canonical function expression.
-/

-- Proof sketch: specialize Proposition 7.31 to the objective
-- `ψ(t) = ∑ od, d od * shortestPath od t`. The stated positivity and
-- positive-homogeneity hypotheses are exactly the assumptions needed for the normalization
-- argument that identifies the dual value with the reciprocal of the normalized supremum.
/-- Proposition 7.32: for the maximal concurrent flow problem with capacity vector `barf`,
demands `d_{i,j}`, and shortest-path costs `SP_{i,j}(t)`, specializing Proposition 7.31 to the
dual objective `ψ(t) = ∑_{(i,j) ∈ 𝒪𝒟} d_{i,j} SP_{i,j}(t)` identifies the dual value `λ⋆` with
the reciprocal of the supremum of `ψ` on the normalized nonnegative slice `⟪barf, t⟫ = 1`,
which is the textbook formula `ψ⋆ = λ⋆⁻¹`. -/
theorem maximalConcurrentFlow_dualValue_eq_inv_normalizedDualObjectiveSup
    (barf : E) (d : OD → ℝ) (shortestPath : OD → E → ℝ)
    (hbarf_pos_on_orthant :
      ∀ t : E, t ∈ nonnegativeOrthant m → t ≠ 0 → 0 < inner ℝ barf t)
    (hobjective_pos :
      ∀ t : E, t ∈ nonnegativeOrthant m → t ≠ 0 →
        0 < ∑ od, d od * shortestPath od t)
    (hobjective_hom :
      IsPositivelyHomogeneousOn 1 (nonnegativeOrthant m)
        (fun t ↦ ∑ od, d od * shortestPath od t)) :
    fractionalCoveringPhiStar barf (fun t ↦ ∑ od, d od * shortestPath od t) =
      (fractionalCoveringNormalizedPsiSup
        barf (fun t ↦ ∑ od, d od * shortestPath od t))⁻¹ := by
  simpa using fractionalCoveringPhiStar_eq_inv_normalizedPsiSup
    barf
    (fun t ↦ ∑ od, d od * shortestPath od t)
    hbarf_pos_on_orthant
    hobjective_pos
    hobjective_hom
