/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_52

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Algorithm 6.4: a conditional-gradient method for the composite objective `f + Ψ` on a convex
feasible set `Q` consists of a feasible starting point `x₀`, step sizes `τ_t ∈ (0, 1]`, the
Chapter 6 linear optimization oracle `v_Ψ`, and a continuous within-gradient field for `f` on
`Q`. The iterates are then the recursively defined feasible points
`x_{t+1} = (1 - τ_t) x_t + τ_t v_Ψ(∇_Q f(x_t))`, where
`v_Ψ(∇_Q f(x_t)) ∈ argmin_{x ∈ Q} {⟨∇_Q f(x_t), x⟩ + Ψ(x)}`. -/
structure LinearOracleCompositeMethod
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) where
  /-- The feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ Q
  /-- The prescribed starting point `x₀`. -/
  x0 : Q
  /-- The step-size sequence `τ₀, τ₁, τ₂, ...`. -/
  stepSize : ℕ → ℝ
  /-- Each step size belongs to `(0, 1]`. -/
  stepSize_mem_Ioc : ∀ t : ℕ, stepSize t ∈ Set.Ioc (0 : ℝ) 1
  /-- The Chapter 6 linear optimization oracle `v_Ψ`. -/
  oracle : StrongDual ℝ E → Q
  /-- The oracle values lie in the canonical argmin sets of the linearized composite oracle
  objective on `Q`. -/
  oracle_spec : IsLinearOptimizationOracle Ψ oracle
  /-- The smooth part has the canonical within-gradient at every feasible point. -/
  hasGradientWithinAt :
    ∀ x : Q, HasGradientWithinAt f (gradientWithin f Q x) Q x
  /-- The canonical within-gradient field is continuous on the feasible set. -/
  gradientWithin_continuousOn : ContinuousOn (gradientWithin f Q) Q

namespace LinearOracleCompositeMethod

variable {Q : Set E} {f : E → ℝ} {Ψ : Q → ℝ}

/-- The iterate sequence of Algorithm 6.4 is defined recursively from `x₀`, the step sizes, and
the Chapter 6 oracle values. -/
def iterates (method : LinearOracleCompositeMethod Q f Ψ) : ℕ → Q
  | 0 => method.x0
  | t + 1 =>
      ⟨(1 - method.stepSize t) • (iterates method t : E) +
          method.stepSize t •
            (method.oracle
              (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q (iterates method t))) : E),
        by
          have hτ_nonneg : 0 ≤ method.stepSize t := (method.stepSize_mem_Ioc t).1.le
          have hτ_le_one : method.stepSize t ≤ 1 := (method.stepSize_mem_Ioc t).2
          have h_one_sub_nonneg : 0 ≤ 1 - method.stepSize t := sub_nonneg.mpr hτ_le_one
          refine
            method.feasibleSet_convex (iterates method t).2
              (method.oracle
                (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q (iterates method t)))).2
              h_one_sub_nonneg hτ_nonneg ?_
          ring⟩

/-- The oracle point at iteration `t` is the Chapter 6 oracle value at the linear functional
defined by the canonical within-gradient of `f` at `x_t`. -/
def oraclePoint
    (method : LinearOracleCompositeMethod Q f Ψ) (t : ℕ) : Q :=
  method.oracle (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q (iterates method t)))

/-- A linear-oracle composite method can be used as its iterate sequence. -/
instance : CoeFun (LinearOracleCompositeMethod Q f Ψ) (fun _ ↦ ℕ → Q) where
  coe method := iterates method

/-- The first iterate of the method is the prescribed starting point `x₀`. -/
@[simp] theorem iterates_zero
    (method : LinearOracleCompositeMethod Q f Ψ) :
    method 0 = method.x0 :=
  rfl

/-- The oracle point at iteration `t` belongs to the canonical argmin set of the Chapter 6
linearized composite oracle objective on `Q`. -/
theorem oraclePoint_mem_argmin
    (method : LinearOracleCompositeMethod Q f Ψ) (t : ℕ) :
    method.oraclePoint t ∈ argmin[Set.univ]
      (linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q (method t))) Ψ) :=
  method.oracle_spec _

/-- The iterate update is
`x_{t+1} = (1 - τ_t) x_t + τ_t v_Ψ(∇_Q f(x_t))`. -/
@[simp] theorem iterates_succ
    (method : LinearOracleCompositeMethod Q f Ψ) (t : ℕ) :
    ((method (t + 1) : Q) : E) =
      (1 - method.stepSize t) • (method t : E) + method.stepSize t • (method.oraclePoint t : E) :=
  rfl

/-- The oracle point at iteration `t` minimizes the linearized composite oracle objective on the
feasible subtype `Q`. -/
theorem oraclePoint_isMinOn
    (method : LinearOracleCompositeMethod Q f Ψ) (t : ℕ) :
    IsMinOn
      (linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q (method t))) Ψ)
      Set.univ
      (method.oraclePoint t) :=
  (mem_constrainedArgmin_iff.mp (method.oraclePoint_mem_argmin t)).2

/-- At every iteration, the oracle point has linearized composite objective value at most that of
any other feasible point. -/
theorem oraclePoint_linearOptimizationOracleObjective_le
    (method : LinearOracleCompositeMethod Q f Ψ) (t : ℕ) (x : Q) :
    linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q (method t))) Ψ
        (method.oraclePoint t) ≤
      linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q (method t))) Ψ x :=
  isMinOn_univ_iff.mp (method.oraclePoint_isMinOn t) x

/-- The oracle point used at iteration `t` belongs to the feasible set `Q`. -/
theorem oraclePoint_mem_feasibleSet
    (method : LinearOracleCompositeMethod Q f Ψ) (t : ℕ) :
    (method.oraclePoint t : E) ∈ Q :=
  (method.oraclePoint t).2

/-- Every iterate produced by the method belongs to the feasible set `Q`. -/
theorem iterates_mem_feasibleSet
    (method : LinearOracleCompositeMethod Q f Ψ) (t : ℕ) :
    (method t : E) ∈ Q :=
  (method t).2

end LinearOracleCompositeMethod

end
