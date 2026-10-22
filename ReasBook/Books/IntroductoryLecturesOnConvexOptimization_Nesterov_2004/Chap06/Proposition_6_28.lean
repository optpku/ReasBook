/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped StandardSimplex

section

variable (n : ℕ) (m : ℕ+)

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 6.28 lies in the finite simplex / entropy-smoothed primal-dual gap domain.

Sampled owner declarations:
* `maxTypeObjective` in `Chap02/Lemma_2_18`, the canonical finite-family maximum owner;
* `Δ[m]` in `Chap06/Definition_6_11`, the Chapter 6 simplex surface for the dual feasible set;
* `normalizedEntropyProxFunction` and `sSup_range_normalizedEntropyProxFunction_eq_log` in
  `Chap06/Definition_6_14` and `Chap06/Lemma_6_3`, the entropy prox owner and its budget
  `D₂ = log m`;
* `scheme_6_2_37_primal_dual_gap_le_rate` in `Chap06/Theorem_6_2_4`, the generic Chapter 6
  `(6.2.37)` gap-rate theorem.

Best owner abstraction:
* source-facing: the explicit strongly convex max-affine primal objective and its associated dual
  objective on the simplex;
* core/canonical: `maxTypeObjective` for the finite maximum and the Chapter 6 simplex owner
  `Δ[m]`;
* bridge/view: the specialization of the generic `(6.2.37)` rate theorem to the entropy budget
  `log m` and the operator-norm formula `‖A‖_{1,2} = max_j ‖g_j‖`.

Primitive data:
* the affine data `f`, `g`, and `points`;
* the explicit primal objective and associated dual objective;
* the scalar operator norm `‖A‖_{1,2}` written directly as `max_j ‖g_j‖`.

Derived API:
* the coordinate expansion of the primal objective;
* the explicit formula for the dual objective;
* the Chapter 6 gap-rate specialization stated in the main theorem below.
-/

/-- The strongly convex max-affine objective
`x ↦ (1 / 2) ‖x‖^2 + max_j (f_j + ⟪g_j, x - x_j⟫)` from Proposition 6.28. -/
def strongly_convex_max_affine_objective
    (f : Fin (m : ℕ) → ℝ) (g points : Fin (m : ℕ) → E) : E → ℝ :=
  fun x ↦
    (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) +
      maxTypeObjective (fun j : Fin (m : ℕ) ↦ fun y : E ↦ f j + inner ℝ (g j) (y - points j)) x

-- Proof sketch: unfold `strongly_convex_max_affine_objective` and then expand the finite maximum
-- by `maxTypeObjective_apply`.
/-- Evaluating `strongly_convex_max_affine_objective` gives the textbook formula
`(1 / 2) ‖x‖^2 + max_j (f_j + ⟪g_j, x - x_j⟫)`. -/
theorem strongly_convex_max_affine_objective_apply
    (f : Fin (m : ℕ) → ℝ) (g points : Fin (m : ℕ) → E) (x : E) :
    strongly_convex_max_affine_objective n m f g points x =
      (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) +
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (m : ℕ) ↦ f j + inner ℝ (g j) (x - points j)) := by
  -- Expand the finite max owner to recover the textbook display formula.
  simp [strongly_convex_max_affine_objective, maxTypeObjective_apply]

/-- The scalar operator norm `‖A‖_{1,2}` from Proposition 6.28, which in the Euclidean primal
geometry equals `max_j ‖g_j‖`. -/
def strongly_convex_max_affine_operator_norm_12
    (g : Fin (m : ℕ) → E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (m : ℕ) ↦ ‖g j‖)

-- Proof sketch: unfold `strongly_convex_max_affine_operator_norm_12`; the displayed finite
-- maximum is the defining formula.
/-- Expanding `strongly_convex_max_affine_operator_norm_12` gives `max_j ‖g_j‖`. -/
theorem strongly_convex_max_affine_operator_norm_12_def
    (g : Fin (m : ℕ) → E) :
    strongly_convex_max_affine_operator_norm_12 n m g =
      Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (m : ℕ) ↦ ‖g j‖) := by
  -- This displayed norm formula is exactly the definition.
  rfl

/-- The associated dual objective
`u ↦ -(1 / 2) ‖Aᵀ u‖^2 - ⟨b, u⟩`, where
`Aᵀ u = ∑_j u_j g_j` and `b_j = ⟪g_j, x_j⟫ - f_j`. -/
def strongly_convex_max_affine_dual_objective
    (f : Fin (m : ℕ) → ℝ) (g points : Fin (m : ℕ) → E) : Δ[m] → ℝ :=
  fun u ↦
    -((1 / 2 : ℝ) * ‖∑ j : Fin (m : ℕ), u j • g j‖ ^ (2 : ℕ)) -
      ∑ j : Fin (m : ℕ), u j * (inner ℝ (g j) (points j) - f j)

-- Proof sketch: unfold `strongly_convex_max_affine_dual_objective`; the displayed formula is the
-- defining expression for the associated dual objective.
/-- Evaluating `strongly_convex_max_affine_dual_objective` recovers the formula
`-(1 / 2) ‖∑_j u_j g_j‖^2 - ∑_j u_j (⟪g_j, x_j⟫ - f_j)`. -/
theorem strongly_convex_max_affine_dual_objective_apply
    (f : Fin (m : ℕ) → ℝ) (g points : Fin (m : ℕ) → E) (u : Δ[m]) :
    strongly_convex_max_affine_dual_objective n m f g points u =
      -((1 / 2 : ℝ) * ‖∑ j : Fin (m : ℕ), u j • g j‖ ^ (2 : ℕ)) -
        ∑ j : Fin (m : ℕ), u j * (inner ℝ (g j) (points j) - f j) := by
  -- Unfold the dual objective to expose the concrete simplex formula from the source.
  rfl

-- Proof sketch: specialize the Chapter 6 rate theorem for scheme `(6.2.37)` to the objective
-- `strongly_convex_max_affine_objective n m f g points`, the associated dual objective
-- `strongly_convex_max_affine_dual_objective n m f g points`, the entropy budget
-- `D₂ = log m`, and the smoothness constant
-- `L₂(φ) = (strongly_convex_max_affine_operator_norm_12 n m g)^2`.
/-- Proposition 6.28 [Chapter6_2.json:92]: for the objective
`x ↦ (1 / 2) ‖x‖^2 + max_j (f_j + ⟪g_j, x - x_j⟫)` and the associated dual objective
`u ↦ -(1 / 2) ‖∑_j u_j g_j‖^2 - ∑_j u_j (⟪g_j, x_j⟫ - f_j)`, if the averaged iterates of
scheme `(6.2.37)` satisfy the entropy-smoothed lower approximation with budget `μ log m` and the
stagewise excessive-gap inequality at
`μ₂,k = 4 ‖A‖_{1,2}^2 / ((k + 1) (k + 2))`, then
`f(x̄_k) - φ(ū_k) ≤ 4 log m · ‖A‖_{1,2}^2 / ((k + 1) (k + 2))`. -/
theorem strongly_convex_max_affine_primal_dual_gap_le_entropy_rate
    (f : Fin (m : ℕ) → ℝ) (g points : Fin (m : ℕ) → E)
    (fμ₂ : ℝ → E → ℝ) (barx : ℕ → E) (baru : ℕ → Δ[m])
    (happrox :
      ∀ μ x,
        strongly_convex_max_affine_objective n m f g points x - μ * Real.log (m : ℝ) ≤
          fμ₂ μ x)
    (hscheme :
      ∀ k : ℕ,
        fμ₂
            ((4 * (strongly_convex_max_affine_operator_norm_12 n m g) ^ (2 : ℕ)) /
              (((k : ℝ) + 1) * ((k : ℝ) + 2)))
            (barx k) ≤
          strongly_convex_max_affine_dual_objective n m f g points (baru k))
    (k : ℕ) :
    strongly_convex_max_affine_objective n m f g points (barx k) -
        strongly_convex_max_affine_dual_objective n m f g points (baru k) ≤
      (4 * Real.log (m : ℝ) * (strongly_convex_max_affine_operator_norm_12 n m g) ^ (2 : ℕ)) /
        (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  -- Route correction: prove the gap bound by specializing the generic `(6.2.37)` rate theorem,
  -- rather than reproducing the excessive-gap algebra locally.
  -- The generic theorem applies with `D₂ = log m` and `L₂(φ) = ‖A‖_{1,2}^2`.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (scheme_6_2_37_primal_dual_gap_le_rate
      (f := strongly_convex_max_affine_objective n m f g points)
      (φ := strongly_convex_max_affine_dual_objective n m f g points)
      (fμ₂ := fμ₂)
      (barx := barx)
      (baru := baru)
      (L2phi := (strongly_convex_max_affine_operator_norm_12 n m g) ^ (2 : ℕ))
      (D2 := Real.log (m : ℝ))
      happrox
      hscheme
      k)

end
