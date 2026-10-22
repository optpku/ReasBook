/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Assumption_6_3_extra_1
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.Filter.Extr

public section

universe u v

namespace OutputLeastSquares

variable {Q : Type u} {Y : Type v} [NormedAddCommGroup Y]

/-- The Chapter 6 data shared by Lemma 6.3: the regularization-parameter regime,
the indexed output-least-squares formula for `T n`, compatibility between the displayed
residuals using `F` and the objective residuals using `Fn` at both `q n` and `qTrue`,
compatibility of `δ n` with the true datum `F qTrue`, admissibility of `qTrue`, and the
minimizing property of `q n` on `C n`. -/
structure MinimizingSequence
    (F : Q → Y) (Fn : ℕ → Q → Y) (T : ℕ → Q → ℝ) (C : ℕ → Set Q)
    (q : ℕ → Q) (d : ℕ → Y) (J : Q → ℝ) (α δ : ℕ → ℝ) (qTrue : Q) : Prop where
  /-- The asymptotic regime relating `α` and `δ`. -/
  regularization : RegularizationParameterAssumptions α δ
  /-- Each regularization parameter is strictly positive. -/
  alpha_pos (n : ℕ) : 0 < α n
  /-- The `n`-th objective is the residual-square-plus-penalty functional. -/
  objective_eq (n : ℕ) (x : Q) : T n x = ‖Fn n x - d n‖ ^ 2 + α n * J x
  /-- The displayed residual at `q n` agrees with the residual used in `T n`. -/
  q_residual_eq (n : ℕ) : ‖Fn n (q n) - d n‖ = ‖F (q n) - d n‖
  /-- The true datum residual computed with `Fn n` agrees with the displayed residual. -/
  qTrue_residual_eq (n : ℕ) : ‖Fn n qTrue - d n‖ = ‖F qTrue - d n‖
  /-- The data-error sequence records the true datum residuals. -/
  delta_eq (n : ℕ) : δ n = ‖F qTrue - d n‖
  /-- The distinguished point `qTrue` is feasible for every constraint set. -/
  qTrue_mem (n : ℕ) : qTrue ∈ C n
  /-- Each `q n` minimizes `T n` on `C n`. -/
  isMinOn (n : ℕ) : IsMinOn (T n) (C n) (q n)

/-- Build a `MinimizingSequence` from the Chapter 6 objective formula, residual
compatibility, feasibility of `qTrue`, and the minimizing property of `q`. -/
theorem MinimizingSequence.ofObjectiveAndMinimizers
    {F : Q → Y} {Fn : ℕ → Q → Y} {T : ℕ → Q → ℝ} {C : ℕ → Set Q}
    {q : ℕ → Q} {d : ℕ → Y} {J : Q → ℝ} {α δ : ℕ → ℝ} {qTrue : Q}
    (h_regularization : RegularizationParameterAssumptions α δ)
    (h_alpha_pos : (n : ℕ) → 0 < α n)
    (h_objective_eq : (n : ℕ) → (x : Q) → T n x = ‖Fn n x - d n‖ ^ 2 + α n * J x)
    (h_q_residual_eq : (n : ℕ) → ‖Fn n (q n) - d n‖ = ‖F (q n) - d n‖)
    (h_qTrue_residual_eq : (n : ℕ) → ‖Fn n qTrue - d n‖ = ‖F qTrue - d n‖)
    (h_delta_eq : (n : ℕ) → δ n = ‖F qTrue - d n‖)
    (h_qTrue_mem : (n : ℕ) → qTrue ∈ C n)
    (h_isMinOn : (n : ℕ) → IsMinOn (T n) (C n) (q n)) :
    MinimizingSequence F Fn T C q d J α δ qTrue :=
  { regularization := h_regularization
    alpha_pos := h_alpha_pos
    objective_eq := h_objective_eq
    q_residual_eq := h_q_residual_eq
    qTrue_residual_eq := h_qTrue_residual_eq
    delta_eq := h_delta_eq
    qTrue_mem := h_qTrue_mem
    isMinOn := h_isMinOn }

/-- In a minimizing sequence, the `n`-th objective value at `q n` does not exceed the one
at the distinguished feasible point `qTrue`. -/
theorem MinimizingSequence.objective_le_true
    {F : Q → Y} {Fn : ℕ → Q → Y} {T : ℕ → Q → ℝ} {C : ℕ → Set Q}
    {q : ℕ → Q} {d : ℕ → Y} {J : Q → ℝ} {α δ : ℕ → ℝ} {qTrue : Q}
    (h : MinimizingSequence F Fn T C q d J α δ qTrue) (n : ℕ) :
    T n (q n) ≤ T n qTrue :=
  (isMinOn_iff.mp (h.isMinOn n)) qTrue (h.qTrue_mem n)

end OutputLeastSquares
