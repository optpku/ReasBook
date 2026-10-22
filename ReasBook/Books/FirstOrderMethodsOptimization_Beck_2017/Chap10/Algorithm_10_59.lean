/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_12
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ProximalPoint

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Algorithm 10.59 is `source-facing` in the constrained smoothing subsection.

Domain sampling in the local Chapter 10 and Chapter 6 API identifies the canonical owners already
present in the workspace:
- `Function.toEReal` from Definition 9.2 is the owner of the canonical coercion from real-valued
  objectives to the extended-real codomain, together with the derived proper/lower-semicontinuous/
  convex bridge API used by the proximal-point owner;
- `proximal_point_operator` / `proxₚ[μ, h.toEReal]` from Definition 10.12 is the point-valued
  bridge surface for `prox_(μ h)`;
- `metricProjection` from Proposition 3.12 is the point-valued owner of `P_C`;
- `fista_momentum_update` and `fista_extrapolated_point` from Algorithm 10.13 are the scalar and
  affine owners of the FISTA momentum recursion and extrapolation rule;
- `IsConvexLipschitzConstrainedMinimizationProblem` from Definition 10.59 is the source-facing
  problem-data owner for the constrained convex Lipschitz setting, and its derived typeclass API
  supplies the closed/convex/proper/low-semicontinuous assumptions needed by the recursion;
- `PosReal` from Definition 6.7 is the canonical owner for the positive source parameters
  `ε`, `μ`, `L̃`, and the positive constant `ℓ_h` appearing in the displayed formulas.

The source item gives an explicit recursive algorithm with named iterates `x^k`, `y^k`, and
`t_k`, but `y^k` is derived from the standard FISTA extrapolation formula once one keeps the
canonical FISTA state `(x^(k-1), x^k, t_k)`. The faithful public interface is therefore the
recursive state owner `constrained_s_fista` valued in `FISTAState E`, together with the
source-facing feasible iterate, extrapolated-point, and momentum companions. The recursive owner
should therefore take the constrained problem data through Definition 10.59's canonical class
rather than restating parallel low-level assumptions about `C` and `h.toEReal`. Since the
displayed initialization uses `μ = ε / ℓ_h^2` and
`L̃ = ℓ_h^2 / ε`, the interface keeps those two positive parameters as named source-facing
declarations rather than hiding them inside the state update. -/

/-- The smoothing parameter `μ = ε / ℓ_h²` appearing in Algorithm 10.59. -/
def constrained_s_fista_smoothing_parameter
    (ε ℓh : PosReal) : PosReal :=
  ⟨(ε : ℝ) / (ℓh : ℝ) ^ (2 : ℕ), by
    have hsq : 0 < (ℓh : ℝ) ^ (2 : ℕ) := by
      have hℓh : 0 < (ℓh : ℝ) := PosReal.coe_pos ℓh
      nlinarith
    exact div_pos (PosReal.coe_pos ε) hsq⟩

-- Proof sketch: unfold `constrained_s_fista_smoothing_parameter`; its real value is
-- definitionally `ε / ℓ_h²`.
/-- Coercing the constrained S-FISTA smoothing parameter to `ℝ` recovers the formula
`μ = ε / ℓ_h²`. -/
@[simp] theorem constrained_s_fista_smoothing_parameter_coe
    (ε ℓh : PosReal) :
    ((constrained_s_fista_smoothing_parameter ε ℓh : PosReal) : ℝ) =
      (ε : ℝ) / (ℓh : ℝ) ^ (2 : ℕ) :=
  rfl

/-- The curvature parameter `L̃ = ℓ_h² / ε` appearing in Algorithm 10.59. -/
def constrained_s_fista_curvature_parameter
    (ε ℓh : PosReal) : PosReal :=
  ⟨(ℓh : ℝ) ^ (2 : ℕ) / (ε : ℝ), by
    have hsq : 0 < (ℓh : ℝ) ^ (2 : ℕ) := by
      have hℓh : 0 < (ℓh : ℝ) := PosReal.coe_pos ℓh
      nlinarith
    exact div_pos hsq (PosReal.coe_pos ε)⟩

-- Proof sketch: unfold `constrained_s_fista_curvature_parameter`; its real value is
-- definitionally `ℓ_h² / ε`.
/-- Coercing the constrained S-FISTA curvature parameter to `ℝ` recovers the formula
`L̃ = ℓ_h² / ε`. -/
@[simp] theorem constrained_s_fista_curvature_parameter_coe
    (ε ℓh : PosReal) :
    ((constrained_s_fista_curvature_parameter ε ℓh : PosReal) : ℝ) =
      (ℓh : ℝ) ^ (2 : ℕ) / (ε : ℝ) :=
  rfl

section Problem

variable (h : E → ℝ) (C : Set E) (ℓh : PosReal)
variable [problem : IsConvexLipschitzConstrainedMinimizationProblem h C (PosReal.toNNReal ℓh)]

/-- The projected proximal step `P_C (prox_(μ h) (y))` used in constrained S-FISTA. -/
def constrained_s_fista_next_iterate
    (ε : PosReal) (y : E) : C :=
  let _ : IsProperExtendedRealFunction h.toEReal :=
    problem.objective_toEReal_proper
  let _ : Fact (LowerSemicontinuous h.toEReal) :=
    ⟨problem.objective_toEReal_lowerSemicontinuous⟩
  let _ : Fact (is_convex_function h.toEReal) :=
    ⟨problem.objective_toEReal_convex⟩
  metricProjection C problem.constraint_nonempty problem.constraint_closed
    problem.constraint_convex
    (proxₚ[constrained_s_fista_smoothing_parameter ε ℓh, h.toEReal] y)

/-- Algorithm 10.59: for a constrained convex Lipschitz problem `min {h(x) | x ∈ C}`, an
accuracy parameter `ε > 0`, and an initial feasible point `x^0 ∈ C`, the constrained S-FISTA
state sequence is expressed through the chapter's canonical FISTA owner `FISTAState E`,
representing `(x^(k-1), x^k, t_k)`. It starts from `x^(-1) = x^0`, `t_0 = 1`, uses the source
parameters `μ = ε / ℓ_h²` and `L̃ = ℓ_h² / ε`, and recursively applies the projected-proximal
update `x^(k+1) = P_C (prox_(μ h) (y^k))`, where `y^k` is the associated FISTA extrapolated
point. -/
def constrained_s_fista
    (ε : PosReal) (x0 : C) : ℕ → FISTAState E
  | 0 =>
      { xPrev := x0
        xCur := x0
        tCur := 1 }
  | k + 1 =>
      let state := constrained_s_fista ε x0 k
      let xNext := constrained_s_fista_next_iterate h C ℓh ε (fista_extrapolated_point state)
      { xPrev := state.xCur
        xCur := xNext
        tCur := fista_momentum_update state.tCur }

/-- The constrained S-FISTA state sequence starts from
`(x^(-1), x^0, t_0) = (x^0, x^0, 1)`. -/
@[simp] theorem constrained_s_fista_zero
    (ε : PosReal) (x0 : C) :
    constrained_s_fista h C ℓh ε x0 0 =
      { xPrev := x0
        xCur := x0
        tCur := 1 } :=
  rfl

/-- Each constrained S-FISTA successor state is obtained from the previous state by the projected
proximal update and the canonical FISTA momentum update. -/
theorem constrained_s_fista_succ
    (ε : PosReal) (x0 : C) (k : ℕ) :
    constrained_s_fista h C ℓh ε x0 (k + 1) =
      let state := constrained_s_fista h C ℓh ε x0 k
      let xNext := constrained_s_fista_next_iterate h C ℓh ε (fista_extrapolated_point state)
      { xPrev := state.xCur
        xCur := xNext
        tCur := fista_momentum_update state.tCur } :=
  rfl

/-- Every constrained S-FISTA current iterate belongs to the feasible set `C`. -/
theorem constrained_s_fista_mem_constraint
    (ε : PosReal) (x0 : C) (k : ℕ) :
    (constrained_s_fista h C ℓh ε x0 k).xCur ∈ C := by
  induction k with
  | zero =>
      simp [constrained_s_fista]
  | succ k hk =>
      simp [constrained_s_fista]

/-- The feasible constrained S-FISTA iterate sequence `x^k`. -/
def constrained_s_fista_x
    (ε : PosReal) (x0 : C) : ℕ → C :=
  fun k ↦
    ⟨(constrained_s_fista h C ℓh ε x0 k).xCur,
      constrained_s_fista_mem_constraint h C ℓh ε x0 k⟩

/-- The ambient-space constrained S-FISTA iterate sequence `x^k`, obtained by coercing the
feasible iterates into `E` for affine formulas such as the FISTA extrapolation rule. -/
def constrained_s_fista_x_point
    (ε : PosReal) (x0 : C) : ℕ → E :=
  fun k ↦ constrained_s_fista_x h C ℓh ε x0 k

/-- The constrained S-FISTA extrapolated sequence `y^k`. -/
def constrained_s_fista_y
    (ε : PosReal) (x0 : C) : ℕ → E :=
  fun k ↦ fista_extrapolated_point (constrained_s_fista h C ℓh ε x0 k)

/- The constrained S-FISTA momentum sequence is the canonical Chapter 10 FISTA momentum
sequence. -/
recall fista_momentum_sequence

/- Its initialization and recursion are reused directly on the constrained S-FISTA theorem
surface. -/
recall fista_momentum_sequence_zero
recall fista_momentum_sequence_succ

/-- The momentum field carried by the constrained S-FISTA state is the canonical Chapter 10 FISTA
momentum sequence. -/
theorem constrained_s_fista_tCur_eq
    (ε : PosReal) (x0 : C) (k : ℕ) :
    (constrained_s_fista h C ℓh ε x0 k).tCur = fista_momentum_sequence k := by
  induction k with
  | zero =>
      simp [constrained_s_fista, fista_momentum_sequence]
  | succ k hk =>
      rw [constrained_s_fista, hk, fista_momentum_sequence_succ]

-- Proof sketch: unfold `constrained_s_fista` at `0`; the initial state's feasible iterate is
-- definitionally `x^0`.
/-- The constrained S-FISTA feasible sequence starts at the prescribed initial point `x^0`. -/
@[simp] theorem constrained_s_fista_x_zero
    (ε : PosReal) (x0 : C) :
    constrained_s_fista_x h C ℓh ε x0 0 = x0 := by
  apply Subtype.ext
  simp [constrained_s_fista_x, constrained_s_fista]

-- Proof sketch: unfold `constrained_s_fista` at `0`; the initial state records `y^0 = x^0`.
/-- The constrained S-FISTA extrapolated sequence starts from `y^0 = x^0`. -/
@[simp] theorem constrained_s_fista_y_zero
    (ε : PosReal) (x0 : C) :
    constrained_s_fista_y h C ℓh ε x0 0 =
      constrained_s_fista_x_point h C ℓh ε x0 0 := by
  simp [constrained_s_fista_y, constrained_s_fista_x_point, constrained_s_fista_x,
    constrained_s_fista, fista_extrapolated_point, fista_momentum_update]

-- Proof sketch: unfold `constrained_s_fista` at `k + 1`; the updated state's `xCur` field is
-- definitionally `P_C (prox_(μ h) (y^k))`.
/-- Each constrained S-FISTA successor iterate satisfies
`x^(k+1) = P_C (prox_(μ h) (y^k))`. -/
theorem constrained_s_fista_x_succ
    (ε : PosReal) (x0 : C) (k : ℕ) :
    constrained_s_fista_x h C ℓh ε x0 (k + 1) =
      constrained_s_fista_next_iterate h C ℓh ε
        (constrained_s_fista_y h C ℓh ε x0 k) := by
  apply Subtype.ext
  simp [constrained_s_fista_x, constrained_s_fista, constrained_s_fista_y]

-- Proof sketch: unfold `constrained_s_fista` at `k + 1`; the updated state's `yCur` field is
-- definitionally the FISTA extrapolation formula built from `x^(k+1)`, `x^k`, `t_(k+1)`, and
-- `t_(k+2)`.
/-- The constrained S-FISTA extrapolated sequence satisfies
`y^(k+1) = x^(k+1) + ((t_(k+1) - 1) / t_(k+2)) (x^(k+1) - x^k)`. -/
theorem constrained_s_fista_y_succ
    (ε : PosReal) (x0 : C) (k : ℕ) :
    constrained_s_fista_y h C ℓh ε x0 (k + 1) =
      constrained_s_fista_x_point h C ℓh ε x0 (k + 1) +
        ((fista_momentum_sequence (k + 1) - 1) /
            fista_momentum_sequence (k + 2)) •
          (constrained_s_fista_x_point h C ℓh ε x0 (k + 1) -
            constrained_s_fista_x_point h C ℓh ε x0 k) := by
  rw [constrained_s_fista_y, fista_extrapolated_point_eq]
  have ht :
      (constrained_s_fista h C ℓh ε x0 (k + 1)).tCur =
        fista_momentum_sequence (k + 1) :=
    constrained_s_fista_tCur_eq h C ℓh ε x0 (k + 1)
  have htNext :
      fista_momentum_update ((constrained_s_fista h C ℓh ε x0 (k + 1)).tCur) =
        fista_momentum_sequence (k + 2) := by
    rw [ht, ← fista_momentum_sequence_succ (k + 1)]
  have hxPrev :
      (constrained_s_fista h C ℓh ε x0 (k + 1)).xPrev =
        constrained_s_fista_x_point h C ℓh ε x0 k := by
    rfl
  rw [htNext, ht, hxPrev]
  simp [constrained_s_fista_x_point, constrained_s_fista_x]

end Problem

end

end
