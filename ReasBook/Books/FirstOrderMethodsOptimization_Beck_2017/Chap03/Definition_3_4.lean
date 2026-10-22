/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 3.4 is `source-facing` in the inequality-constrained duality API. Its primitive data
are the Lagrangian and the resulting dual objective. Chapter 2's `effective_domain` remains the
owner abstraction for finite-valued loci, but the multiplier nonnegativity condition belongs to
the separate source-facing dual-domain layer rather than being folded into the dual objective
itself. Accordingly, `q` is the raw Lagrangian infimum, while the admissible dual multipliers are
described by coordinatewise nonnegativity together with lower-finiteness of `q`. -/

section

variable {E : Type u} {m : ℕ}
variable (X : Set E) (f : E → ℝ) (g : E → EuclideanSpace ℝ (Fin m))

local notation "MultiplierSpace" => EuclideanSpace ℝ (Fin m)

/-- The Lagrangian associated to `f`, the inequality-constraint map `g`, and a multiplier vector. -/
def lagrangian (multiplier : MultiplierSpace) : E → ℝ :=
  fun x ↦ f x + dotProduct multiplier (g x)

-- Proof sketch: unfold `lagrangian`; the statement is exactly its defining formula.
/-- The Lagrangian is the objective value plus the Euclidean pairing of the multiplier with the
constraint vector. -/
@[simp] theorem lagrangian_apply (multiplier : MultiplierSpace) (x : E) :
    lagrangian f g multiplier x = f x + dotProduct multiplier (g x) :=
  rfl

/-- Definition 3.4: the Lagrangian dual objective function of the constrained problem
`min {f x : g x ≤ 0, x ∈ X}`. It is the infimum of the Lagrangian over `X`; the coordinatewise
nonnegativity restriction on multipliers is imposed separately in the dual-domain layer. -/
def lagrangian_dual_objective (multiplier : MultiplierSpace) : EReal :=
  sInf ((fun x : E ↦ (lagrangian f g multiplier x : EReal)) '' X)

-- Proof sketch: unfold `lagrangian_dual_objective`; the statement is exactly its defining
-- infimum formula.
/-- Evaluating the dual objective at a multiplier gives the infimum of the `EReal`-valued
Lagrangian over `X`. -/
theorem lagrangian_dual_objective_eq_sInf
    (multiplier : MultiplierSpace) :
    lagrangian_dual_objective X f g multiplier =
      sInf ((fun x : E ↦ (lagrangian f g multiplier x : EReal)) '' X) :=
  rfl

/-- The source-facing dual domain consists of the coordinatewise nonnegative multipliers at which
the negated dual objective belongs to the Chapter 2 owner `effective_domain`. -/
def lagrangian_dual_effective_domain : Set MultiplierSpace :=
  {multiplier | ∀ i : Fin m, 0 ≤ multiplier i} ∩
    effective_domain (fun μ ↦ -lagrangian_dual_objective X f g μ)

-- Proof sketch: unfold `lagrangian_dual_effective_domain` to `effective_domain (-q)` and use the
-- `EReal` identity `-q(λ) < ⊤ ↔ q(λ) ≠ ⊥ ↔ ⊥ < q(λ)`.
/-- A multiplier lies in `dom (-q)` exactly when it is coordinatewise nonnegative and the dual
objective is greater than `-∞` there. -/
@[simp] theorem mem_lagrangian_dual_effective_domain
    (multiplier : MultiplierSpace) :
    multiplier ∈ lagrangian_dual_effective_domain X f g ↔
      (∀ i : Fin m, 0 ≤ multiplier i) ∧ ⊥ < lagrangian_dual_objective X f g multiplier := by
  simp [lagrangian_dual_effective_domain, effective_domain, lt_top_iff_ne_top,
    EReal.neg_eq_top_iff, bot_lt_iff_ne_bot]

end
