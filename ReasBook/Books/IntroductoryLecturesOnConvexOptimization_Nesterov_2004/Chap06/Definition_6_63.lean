/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u v

section Normed

variable {E : Type u} {E₂ : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-
Definition 6.63 lies in the Chapter 6 max-representation / dual-uniform-convexity domain.

Sampled owner-style declarations:
- `UniformConvexOn` and `UniformConvexOn.lower_tangent_power` in
  `Chap04/Definition_4_2_8`, the project owner/bridge for degree-`p` uniform convexity on a set;
- `smoothedPrimalObjectiveMaximand` in `Definition_6_30`, the chapter owner for dual maximands of
  the form `u ↦ (A x) u - \hat φ(u) - μ d(u)`;
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the chapter owner for the feasible argmax
  set of such maximands;
- `mem_smoothedPrimalObjectiveArgmax_iff` in `Definition_6_30`, the canonical bridge to the raw
  feasibility-and-`IsMaxOn` condition;
- `MaxRepresentationOracle` in `Chap03/Definition_3_29`, showing the project pattern of keeping a
  source-facing oracle while expressing its maximizer data through a canonical owner.

Best owner abstraction:
- source-facing: `IsMaxRepresentationWithUniformlyConvexDualTerm`;
- core/canonical: `UniformConvexOn Qd (uniformConvexPowerModulus σg p) g`,
  `smoothedPrimalObjective`, `smoothedPrimalObjectiveMaximand`, and
  `smoothedPrimalObjectiveArgmax` specialized to zero smooth part and zero prox term;
- bridge/view: the derived theorems below turning owner-based argmax membership back into the
  textbook formulas `f x = (A x) (u x) - g (u x)`, uniqueness of the maximizer, and the
  first-order lower-support inequality for the dual term.

Primitive data:
- the dual feasible-set geometry of `Qd`;
- differentiability of `g` on `Qd`;
- the canonical Chapter 4 owner `UniformConvexOn Qd (uniformConvexPowerModulus σg p) g`;
- a chosen selector `u`;
- the represented objective equality `f x = sup_{v ∈ Qd} ((A x) v - g v)`;
- membership of the chosen point in the canonical argmax owner.

Derived API:
- convexity of `Qd`, already packaged by `UniformConvexOn`;
- the chapter's first-order lower-support inequality for `g` on `Qd`;
- the textbook argmax-value formula;
- the pointwise domination inequality `(A x) v - g v ≤ f x`;
- strict convexity of `g` and strict concavity of the dual maximand on `Qd`;
- the textbook uniqueness statement for any feasible maximizer written in ambient terms.

The previous file rebuilt a local maximand owner duplicating `Definition_6_30` and kept the dual
uniform-convexity data as a bespoke gradient-monotonicity field. This refinement keeps Definition
6.63 source-facing, but moves the maximizer data to the Chapter 6 owner surface and the dual-term
geometry to the Chapter 4 owner surface. The unique-maximizer clause is now derived from strict
concavity of the canonical maximand instead of being stored as primitive data.
-/

/-- Definition 6.63: `f` has a max-representation with `p`-uniformly convex dual term when there
is a nonempty closed convex dual set `Q_d`, a differentiable dual term `g`, and a maximizer
selection `u(x)` such that `f x = max_{u ∈ Q_d} ((A x) u - g u)`, the maximizer is unique, and
`g` is uniformly convex on `Q_d` with power modulus
`r ↦ (1 / p) * σ_g * r^p` for some `p ≥ 2` and `σ_g > 0`. -/
class IsMaxRepresentationWithUniformlyConvexDualTerm
    (f : E → ℝ) (A : E →L[ℝ] StrongDual ℝ E₂) (Qd : Set E₂)
    (g : E₂ → ℝ) (u : E → E₂) (p σg : ℝ) : Prop where
  /-- The dual feasible set `Q_d` is nonempty. -/
  dualSet_nonempty : Qd.Nonempty
  /-- The dual feasible set `Q_d` is closed. -/
  dualSet_closed : IsClosed Qd
  /-- The dual term `g` is differentiable on `Q_d`. -/
  dualTerm_differentiableOn : DifferentiableOn ℝ g Qd
  /-- The exponent in the dual uniform-convexity inequality satisfies `p ≥ 2`. -/
  two_le_degree : 2 ≤ p
  /-- The dual uniform-convexity parameter is positive. -/
  dualParameter_pos : 0 < σg
  /-- The dual term is uniformly convex on `Q_d` with the Chapter 4 power modulus owner. -/
  dualTerm_uniformConvexOn :
    UniformConvexOn Qd (uniformConvexPowerModulus σg p) g
  /-- The chosen maximizer belongs to the canonical Chapter 6 argmax owner for the zero-smoothed
  maximand `v ↦ (A x) v - g v`. -/
  argmax_mem (x : E) :
    u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x
  /-- The represented objective agrees with the canonical Chapter 6 supremum owner for the same
  zero-smoothed maximand. -/
  objective_eq (x : E) :
    f x = smoothedPrimalObjective A Qd 0 g 0 0 x

/-- A max-representation with uniformly convex dual term canonically supplies the full owner-level
payload: the dual-term uniform convexity and the chosen argmax/value identities. -/
instance {f : E → ℝ} {A : E →L[ℝ] StrongDual ℝ E₂} {Qd : Set E₂}
    {g : E₂ → ℝ} {u : E → E₂} {p σg : ℝ}
    [h : IsMaxRepresentationWithUniformlyConvexDualTerm f A Qd g u p σg] :
    Fact
      (UniformConvexOn Qd (uniformConvexPowerModulus σg p) g ∧
        ∀ x : E,
          u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x ∧
            f x = smoothedPrimalObjective A Qd 0 g 0 0 x) where
  out := ⟨h.dualTerm_uniformConvexOn, fun x ↦ ⟨h.argmax_mem x, h.objective_eq x⟩⟩

namespace IsMaxRepresentationWithUniformlyConvexDualTerm

variable {f : E → ℝ} {A : E →L[ℝ] StrongDual ℝ E₂} {Qd : Set E₂}
  {g : E₂ → ℝ} {u : E → E₂} {p σg : ℝ}

/-- The dual feasible set `Q_d` is convex because the Chapter 4 owner
`UniformConvexOn Qd (uniformConvexPowerModulus σg p) g` already packages that geometry. -/
theorem dualSet_convex
    (h : IsMaxRepresentationWithUniformlyConvexDualTerm f A Qd g u p σg) :
    Convex ℝ Qd :=
  h.dualTerm_uniformConvexOn.1

/-- The dual term is strictly convex on `Q_d` because the power modulus is strictly positive on
positive norms once `σ_g > 0` and `p ≥ 2`. -/
theorem dualTerm_strictConvexOn
    (h : IsMaxRepresentationWithUniformlyConvexDualTerm f A Qd g u p σg) :
    StrictConvexOn ℝ Qd g := by
  refine ⟨h.dualSet_convex, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have huc := h.dualTerm_uniformConvexOn.2 hx hy ha.le hb.le hab
  have hp : 0 < p := by linarith [h.two_le_degree]
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hnorm : 0 < ‖x - y‖ := by
    exact norm_pos_iff.mpr hxy'
  have hmod : 0 < uniformConvexPowerModulus σg p ‖x - y‖ := by
    have hp_inv : 0 < 1 / p := one_div_pos.mpr hp
    have hrpow : 0 < Real.rpow ‖x - y‖ p := Real.rpow_pos_of_pos hnorm p
    dsimp [uniformConvexPowerModulus]
    exact mul_pos (mul_pos hp_inv h.dualParameter_pos) hrpow
  exact huc.trans_lt (sub_lt_self _ (mul_pos (mul_pos ha hb) hmod))

/-- For each `x`, the canonical dual maximand `v ↦ (A x) v - g v` is strictly concave on `Q_d`. -/
theorem maximand_strictConcaveOn
    (h : IsMaxRepresentationWithUniformlyConvexDualTerm f A Qd g u p σg) (x : E) :
    StrictConcaveOn ℝ Qd (smoothedPrimalObjectiveMaximand A g 0 0 x) := by
  have hlinear : ConcaveOn ℝ Qd fun v : E₂ ↦ (A x) v := by
    simpa using (A x).toLinearMap.concaveOn h.dualSet_convex
  convert hlinear.sub_strictConvexOn h.dualTerm_strictConvexOn using 1
  ext v
  simp [smoothedPrimalObjectiveMaximand]

private theorem argmax_isGreatest
    (h : IsMaxRepresentationWithUniformlyConvexDualTerm f A Qd g u p σg) (x : E) :
    IsGreatest
      (smoothedPrimalObjectiveMaximand A g 0 0 x '' Qd)
      (smoothedPrimalObjectiveMaximand A g 0 0 x (u x)) := by
  rcases
      (mem_smoothedPrimalObjectiveArgmax_iff A Qd g 0 0 x (u x)).mp
        (h.argmax_mem x) with
    ⟨hu_mem, hu_max⟩
  refine ⟨⟨u x, hu_mem, rfl⟩, ?_⟩
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  exact (isMaxOn_iff.mp hu_max) v hv

/-- The chosen point is the unique member of the canonical argmax owner, now derived from strict
concavity of the maximand rather than stored as primitive data. -/
theorem argmax_eq
    (h : IsMaxRepresentationWithUniformlyConvexDualTerm f A Qd g u p σg)
    (x : E) {v : E₂} (hv : v ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x) :
    v = u x := by
  rcases
      (mem_smoothedPrimalObjectiveArgmax_iff A Qd g 0 0 x v).mp hv with
    ⟨hv_mem, hv_max⟩
  rcases
      (mem_smoothedPrimalObjectiveArgmax_iff A Qd g 0 0 x (u x)).mp
        (h.argmax_mem x) with
    ⟨hu_mem, hu_max⟩
  exact (h.maximand_strictConcaveOn x).eq_of_isMaxOn hv_max hu_max hv_mem hu_mem

/-- The chosen maximizer realizes the textbook max-representation value
`f x = (A x) (u x) - g (u x)`. -/
theorem objective_eq_argmax
    (h : IsMaxRepresentationWithUniformlyConvexDualTerm f A Qd g u p σg) (x : E) :
    f x = (A x) (u x) - g (u x) := by
  rw [h.objective_eq x]
  rw [smoothedPrimalObjective_apply]
  rw [(argmax_isGreatest h x).csSup_eq]
  simp [smoothedPrimalObjectiveMaximand]

/-- Every feasible dual point gives a value bounded above by the represented objective. -/
theorem maximand_le_objective
    (h : IsMaxRepresentationWithUniformlyConvexDualTerm f A Qd g u p σg)
    (x : E) {v : E₂} (hv : v ∈ Qd) :
    (A x) v - g v ≤ f x := by
  rcases
      (mem_smoothedPrimalObjectiveArgmax_iff A Qd g 0 0 x (u x)).mp
        (h.argmax_mem x) with
    ⟨_, hu_max⟩
  rw [h.objective_eq_argmax x]
  simpa [smoothedPrimalObjectiveMaximand] using (isMaxOn_iff.mp hu_max) v hv

/-- The chosen maximizer is the unique feasible point attaining the textbook max-representation
value of `f x`. -/
theorem argmax_unique
    (h : IsMaxRepresentationWithUniformlyConvexDualTerm f A Qd g u p σg)
    (x : E) {v : E₂} (hv : v ∈ Qd)
    (hv_eq : (A x) v - g v = f x) :
    v = u x := by
  apply h.argmax_eq x
  rw [mem_smoothedPrimalObjectiveArgmax_iff]
  refine ⟨hv, ?_⟩
  intro w hw
  simpa [smoothedPrimalObjectiveMaximand, ← hv_eq] using h.maximand_le_objective x hw

end IsMaxRepresentationWithUniformlyConvexDualTerm

end Normed

section Hilbert

variable {E : Type u} {E₂ : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

namespace IsMaxRepresentationWithUniformlyConvexDualTerm

variable {f : E → ℝ} {A : E →L[ℝ] StrongDual ℝ E₂} {Qd : Set E₂}
  {g : E₂ → ℝ} {u : E → E₂} {p σg : ℝ}

/-- The Chapter 4 owner recovers the first-order lower-support inequality for the dual term on
`Q_d`. -/
theorem dualTerm_lower_tangent_power
    (h : IsMaxRepresentationWithUniformlyConvexDualTerm f A Qd g u p σg)
    {u₁ u₂ : E₂} (hu₁ : u₁ ∈ Qd) (hu₂ : u₂ ∈ Qd) :
    g u₂ ≥ g u₁ + inner ℝ (gradientWithin g Qd u₁) (u₂ - u₁) +
      uniformConvexPowerModulus σg p ‖u₂ - u₁‖ := by
  exact h.dualTerm_uniformConvexOn.lower_tangent_power
    u₁ hu₁ (h.dualTerm_differentiableOn u₁ hu₁) u₂ hu₂

end IsMaxRepresentationWithUniformlyConvexDualTerm

end Hilbert

end
