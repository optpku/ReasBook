/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap13.Algorithm_13_5
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {n l : ℕ}

local notation "E" => Fin n → ℝ

/- `prompt_add/` is absent in this workspace, so the statement design is checked against the
nearby Chapter 13 owners. This item is `source-facing`: it records the data produced by the
initialization procedure used before the convergence statements.

Domain sampling identifies the relevant owners already present upstream:
- `polytope_quadratic_feasible_set` and `polytope_quadratic_objective` from Definition 13.10 for
  the finite-hull quadratic model on a vertex family `a : Fin l → E`;
- `polytope_quadratic_conditional_gradient_one_step` and
  `polytope_quadratic_vertex_mem_feasible_set` from Algorithm 13.5 for the trial conditional-
  gradient step from the minimizing vertex;
- `IsStrictVertexSublevelInitialPoint` from Assumption 13.18 for the final strict-simplex output.

The `core/canonical` owner in this part of the chapter is the vertex family `a`, not a concrete
matrix whose columns realize that family. Matrix identities such as `x = A *ᵥ v` are therefore
demoted to the usual bridge `a := A.col`, while the public Algorithm 13.6 API records barycentric
equalities directly as weighted sums `∑ i, v i • a i`. The trial step is not stored through a
second local wrapper: it is primitive data only as a feasible-iterate instance of the existing
Algorithm 13.5 one-step owner. -/

/-- Helper for Algorithm 13.6 step 4: if the trial simplex coordinates `ṽ⁰` are already strictly
positive, the algorithm keeps `(x̃⁰, ṽ⁰)`. Otherwise it chooses strictly positive simplex
coordinates `v⁰` close enough to `ṽ⁰` so that the resulting point
`x⁰ = ∑ i, v⁰ i • a i` still satisfies `f_q x⁰ < f_q (a p)`. -/
class algorithm_13_6_step4_output
    (f_q : E → ℝ) (a : Fin l → E)
    (p : Fin l) (xTilde0 x0 : E)
    (vTilde0 v0 : stdSimplex ℝ (Fin l)) where
  /-- The final simplex coordinates produced by step 4 are strictly positive. -/
  final_weights_pos : ∀ i, 0 < v0 i
  /-- If the trial simplex coordinates are already strictly positive, step 4 keeps the trial
  pair. -/
  keep_trial_point :
    (∀ i, 0 < vTilde0 i) →
      v0 = vTilde0 ∧ x0 = xTilde0
  /-- If the trial simplex coordinates are not strictly positive, step 4 supplies a positive
  perturbation radius. -/
  perturbation_radius :
    (¬ ∀ i, 0 < vTilde0 i) → ℝ
  /-- The perturbation radius used on the nonpositive branch is strictly positive. -/
  perturbation_radius_pos :
    ∀ hnot : ¬ ∀ i, 0 < vTilde0 i,
      0 < perturbation_radius hnot
  /-- On the nonpositive branch, the final point is the barycentric combination defined by the
  strictly positive simplex coordinates `v⁰`. -/
  eq_weighted_sum_of_not_weights_pos :
    (¬ ∀ i, 0 < vTilde0 i) →
      x0 = ∑ i, v0 i • a i
  /-- On the nonpositive branch, the chosen strictly positive simplex coordinates stay within the
  perturbation radius of the trial coordinates. -/
  weights_near_of_not_weights_pos :
    ∀ hnot : ¬ ∀ i, 0 < vTilde0 i,
      dist v0 vTilde0 < perturbation_radius hnot
  /-- On the nonpositive branch, the resulting point still has objective value below the
  minimizing vertex `a_p`. -/
  objective_lt_vertex_of_not_weights_pos :
    (¬ ∀ i, 0 < vTilde0 i) →
      f_q x0 < f_q (a p)

variable {f_q : E → ℝ} {a : Fin l → E} {p : Fin l} {xTilde0 x0 : E}
variable {vTilde0 v0 : stdSimplex ℝ (Fin l)}

/-- Initialization data for Algorithm 13.6: `p` minimizes the vertex values `f_q(a_i)`, the point
`x̃⁰` is produced by one Algorithm 13.5 conditional-gradient step from the feasible vertex `a_p`
and strictly improves the objective, `ṽ⁰ ∈ Δ_l` represents `x̃⁰`, and step 4 then either keeps
`(x̃⁰, ṽ⁰)` when `ṽ⁰ ∈ ℝ^l_{++}` or replaces it by a strictly positive simplex point `v⁰` chosen
sufficiently close to `ṽ⁰` so that the strict inequality persists for
`x⁰ = ∑ i, v⁰_i • a_i`. The final output is exposed canonically through
`IsStrictVertexSublevelInitialPoint`. -/
class algorithm_13_6_initialization
    (Q : positiveDefiniteMatrices n) (b : E) (a : Fin l → E)
    (p : Fin l) (xTilde0 x0 : E)
    (vTilde0 v0 : stdSimplex ℝ (Fin l)) where
  minimizing_vertex :
    IsMinOn (fun i : Fin l ↦ polytope_quadratic_objective Q b (a i)) Set.univ p
  trial_eq_weighted_sum :
    xTilde0 = ∑ i, vTilde0 i • a i
  trial_step :
    polytope_quadratic_conditional_gradient_one_step Q b a
      ⟨a p, polytope_quadratic_vertex_mem_feasible_set a p⟩
      ⟨xTilde0,
        weighted_sum_mem_convexHull_range vTilde0
          (fun i ↦ stdSimplex.zero_le _ i)
          (stdSimplex.sum_eq_one vTilde0)
          trial_eq_weighted_sum⟩
  trial_improves :
    polytope_quadratic_objective Q b xTilde0 <
      polytope_quadratic_objective Q b (a p)
  step4 :
    algorithm_13_6_step4_output (polytope_quadratic_objective Q b) a p xTilde0 x0 vTilde0 v0

variable {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E}
variable {p : Fin l} {xTilde0 x0 : E} {vTilde0 v0 : stdSimplex ℝ (Fin l)}

namespace algorithm_13_6_initialization

set_option linter.unusedVariables false in
/-- Algorithm 13.6: an initialization canonically yields Assumption 13.18 for the final output
`(x⁰, v⁰)`. This is the chapter-level `bridge/view` from the procedural initialization data to the
source-facing strict-vertex-sublevel owner. -/
theorem toIsStrictVertexSublevelInitialPoint
    (h : algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0) :
    IsStrictVertexSublevelInitialPoint (polytope_quadratic_objective Q b) a x0 v0 :=
  -- Extract the one comparison with the minimizing vertex that is reused in both step-4 branches.
  let hp_le : ∀ i : Fin l,
      polytope_quadratic_objective Q b (a p) ≤
        polytope_quadratic_objective Q b (a i) :=
    fun i ↦ (isMinOn_iff.mp h.minimizing_vertex) i (Set.mem_univ i)
  { objective_lt_vertex := fun i ↦
      if hpos : ∀ j, 0 < vTilde0 j then
        let hkeep := h.step4.keep_trial_point hpos
        -- On the keep branch, rewrite the final point back to the trial point and combine
        -- the trial improvement with the minimizing-vertex inequality.
        calc
          polytope_quadratic_objective Q b x0
              = polytope_quadratic_objective Q b xTilde0 :=
                congrArg (polytope_quadratic_objective Q b) hkeep.2
          _ < polytope_quadratic_objective Q b (a p) := h.trial_improves
          _ ≤ polytope_quadratic_objective Q b (a i) := hp_le i
      else
        -- On the perturbation branch, step 4 already preserves the strict improvement below `a p`.
        lt_of_lt_of_le (h.step4.objective_lt_vertex_of_not_weights_pos hpos) (hp_le i)
    eq_weighted_sum :=
      if hpos : ∀ j, 0 < vTilde0 j then
        let hkeep := h.step4.keep_trial_point hpos
        -- The final point is either the kept trial barycentric combination or the perturbed one
        -- supplied by step 4.
        calc
          x0 = xTilde0 := hkeep.2
          _ = ∑ i, vTilde0 i • a i := h.trial_eq_weighted_sum
          _ = ∑ i, v0 i • a i :=
            congrArg (fun w : stdSimplex ℝ (Fin l) ↦ ∑ i, w i • a i) hkeep.1.symm
      else
        h.step4.eq_weighted_sum_of_not_weights_pos hpos
    weights_mem_positiveOrthant :=
      -- Step 4 always outputs strictly positive simplex coordinates.
      (mem_positiveOrthant_iff).2 h.step4.final_weights_pos }

/-- An Algorithm 13.6 initialization canonically yields Assumption 13.18 for the final output
`(x⁰, v⁰)`. This is the chapter-level `bridge/view` from the procedural initialization data to the
source-facing strict-vertex-sublevel owner. -/
instance instIsStrictVertexSublevelInitialPoint
    [algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0] :
    IsStrictVertexSublevelInitialPoint (polytope_quadratic_objective Q b) a x0 v0 :=
  -- Reuse the canonical bridge theorem as the instance payload.
  toIsStrictVertexSublevelInitialPoint
    (Q := Q) (b := b) (a := a) (p := p)
    (xTilde0 := xTilde0) (x0 := x0) (vTilde0 := vTilde0) (v0 := v0)
    (inferInstance)

set_option linter.unusedVariables false in
/-- In Algorithm 13.6, the final output has objective value strictly below every vertex value. -/
theorem objective_lt_vertex
    (h : algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0) (i : Fin l) :
    polytope_quadratic_objective Q b x0 < polytope_quadratic_objective Q b (a i) :=
  -- Project the strict vertex comparison from the canonical Assumption 13.18 bridge.
  (toIsStrictVertexSublevelInitialPoint h).objective_lt_vertex i

set_option linter.unusedVariables false in
/-- In Algorithm 13.6, the final output keeps the barycentric representation `x⁰ = ∑ i, v⁰_i a_i`.
-/
theorem eq_weighted_sum
    (h : algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0) :
    x0 = ∑ i, v0 i • a i :=
  -- Project the barycentric representation from the canonical Assumption 13.18 bridge.
  (toIsStrictVertexSublevelInitialPoint h).eq_weighted_sum

set_option linter.unusedVariables false in
/-- In Algorithm 13.6, the final simplex coordinates are strictly positive. -/
theorem weight_pos
    (h : algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0) (i : Fin l) :
    0 < v0 i :=
  -- Project coordinatewise positivity from the canonical Assumption 13.18 bridge.
  (toIsStrictVertexSublevelInitialPoint h).weight_pos i

set_option linter.unusedVariables false in
/-- In Algorithm 13.6, the final output remains in the feasible polytope
`Ω = conv{a₁, …, a_l}`. -/
theorem mem_feasible_set
    (h : algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0) :
    x0 ∈ polytope_quadratic_feasible_set a :=
  (toIsStrictVertexSublevelInitialPoint h).mem_feasible_set

end algorithm_13_6_initialization

end
