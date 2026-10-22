/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 10.12 is `source-facing`: the textbook specifies a fixed positive parameter `c`, an
initial point `x^0 = x0`, and the recursive update `x^{k+1} ∈ prox_{c g}(x^k)`. The canonical
owner for proximal points is the set-valued mapping `prox[...]`, so the weakest source-facing API
is the trajectory predicate below. When stronger hypotheses make each scaled proximal set a
singleton, the file then upgrades to the point-valued operator and recursively chosen iterate
family as a bridge/view, rather than treating those chosen points as primitive data. -/

/-- Definition 10.12: a sequence `x^k` follows the proximal-point method for `g` with parameter
`c > 0` and initial point `x^0 = x0` when it starts at `x0` and each successor iterate belongs to
the scaled proximal set `prox[((c : EReal) • g)] (x^k)`. -/
def is_proximal_point_trajectory
    (g : E → EReal) (x0 : E) (c : PosReal) (x : ℕ → E) : Prop :=
  x 0 = x0 ∧ ∀ k : ℕ, x (k + 1) ∈ prox[((c : EReal) • g)] (x k)

/-- A proximal-point trajectory starts at the prescribed initial point `x^0 = x0`. -/
theorem is_proximal_point_trajectory_zero
    {g : E → EReal} {x0 : E} {c : PosReal} {x : ℕ → E}
    (h : is_proximal_point_trajectory g x0 c x) :
    x 0 = x0 :=
  h.1

/-- At each iteration `k`, a proximal-point trajectory satisfies the canonical scaled-proximal
update rule `x^(k+1) ∈ prox[((c : EReal) • g)] (x^k)`. -/
theorem is_proximal_point_trajectory_step
    {g : E → EReal} {x0 : E} {c : PosReal} {x : ℕ → E}
    (h : is_proximal_point_trajectory g x0 c x) (k : ℕ) :
    x (k + 1) ∈ prox[((c : EReal) • g)] (x k) :=
  h.2 k

section

variable [InnerProductSpace ℝ E] [ProperSpace E]

/- Under the proper closed convex hypotheses used later in Chapter 10, each scaled proximal set is
a singleton. The declarations in this section are therefore `bridge/view`: they refine the
source-facing trajectory owner to a point-valued operator and the recursively chosen sequence
`x^(k+1) = prox_{c g}(x^k)`. -/

private theorem scaled_prox_eq_singleton
    (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] (c : PosReal) (x : E) :
    ∃ u : E, prox[((c : EReal) • g)] x = {u} := by
  have hg_closed : LowerSemicontinuous g := Fact.out
  have hg_convex : is_convex_function g := Fact.out
  rcases scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex c with
    ⟨hg_scaled_proper, hg_scaled_closed, hg_scaled_convex⟩
  exact
    prox_eq_singleton_of_proper_closed_convex
      (((c : EReal) • g))
      hg_scaled_proper
      hg_scaled_closed
      hg_scaled_convex
      x

variable (g : E → EReal) [IsProperExtendedRealFunction g]
variable [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
variable (x0 : E) (c : PosReal)

/-- The one-step proximal-point operator with parameter `c > 0`, namely the unique point of
`prox[(c : EReal) • g] x`. -/
def proximal_point_operator : E → E :=
  fun x ↦ Classical.choose <| scaled_prox_eq_singleton g c x

/- Surface notation for the point-valued proximal update `x ↦ prox_{c g}(x)` attached to the
singleton proximal set `prox[((c : EReal) • g)] x`. The supporting lower-semicontinuity and
convexity assumptions are resolved from the ambient instance context, so the notation keeps only
the mathematical data `c` and `g` on the public surface. -/
@[inherit_doc] scoped[ProximalPoint] notation:max
    "proxₚ[" c ", " g "]" =>
  proximal_point_operator g c

open scoped ProximalPoint

-- Proof sketch: positive scaling by `c` preserves properness, lower semicontinuity, and
-- convexity of `g`; Theorem 6.3 then identifies `prox[(c : EReal) • g] x` as a singleton, and
-- `proximal_point_operator` is defined to be its unique point.
/-- The proximal-point operator is the unique proximal point of the scaled function `c g` at the
base point `x`. -/
theorem proximal_point_operator_eq_singleton (x : E) :
    prox[((c : EReal) • g)] x = {proxₚ[c, g] x} := by
  simpa [proximal_point_operator] using
    (Classical.choose_spec <| scaled_prox_eq_singleton g c x)

/-- The proximal-point operator is a point of the scaled proximal set `prox[c g] x`. -/
@[simp] theorem proximal_point_operator_mem (x : E) :
    proxₚ[c, g] x ∈ prox[((c : EReal) • g)] x := by
  rw [proximal_point_operator_eq_singleton]
  simp

-- Proof sketch: `proximal_point_operator_mem` places the chosen point in the scaled proximal set;
-- the canonical Chapter 6 bridge `isMinOn_moreau_penalty_of_mem_scaled_prox` then converts that
-- proximal membership directly into minimization of the textbook penalized objective.
/-- The proximal-point operator minimizes the textbook penalized objective
`y ↦ g y + (1 / (2 c)) ‖y - x‖²`. -/
theorem proximal_point_operator_isMinOn (x : E) :
    IsMinOn
      (fun y : E ↦ g y + ((((1 / (2 * c) : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal))
      Set.univ
      (proxₚ[c, g] x) := by
  simpa [norm_sub_rev] using
    isMinOn_moreau_penalty_of_mem_scaled_prox (proximal_point_operator_mem g c x)

/-- Definition 10.12: for a proper closed convex objective `g`, an initial point `x^0 = x0`, and
a parameter `c > 0`, the proximal point method is the recursive sequence
`x^(k+1) = prox_{c g}(x^k)`. -/
def proximal_point_method : ℕ → E
  | 0 => x0
  | k + 1 => proxₚ[c, g] (proximal_point_method k)

/-- The recursive proximal-point sequence agrees with the iterate view
`x^k = (prox_{c g})^[k] (x^0)`. -/
theorem proximal_point_method_def :
    proximal_point_method g x0 c =
      fun k ↦ Nat.iterate (proxₚ[c, g]) k x0 :=
  by
    funext k
    induction k with
    | zero => rfl
    | succ k hk =>
        simp [proximal_point_method, hk, Function.iterate_succ_apply']

/-- The proximal-point method starts at the chosen initial point `x0`. -/
@[simp] theorem proximal_point_method_zero :
    proximal_point_method g x0 c 0 = x0 :=
  rfl

/-- Each successor iterate of the proximal point method is obtained by applying the one-step
proximal-point operator to the previous iterate. -/
@[simp] theorem proximal_point_method_succ (k : ℕ) :
    proximal_point_method g x0 c (k + 1) =
      proxₚ[c, g] (proximal_point_method g x0 c k) :=
  rfl

/-- The recursively chosen proximal-point sequence is a proximal-point trajectory for the canonical
scaled proximal-set owner. -/
theorem proximal_point_method_is_proximal_point_trajectory :
    is_proximal_point_trajectory g x0 c (proximal_point_method g x0 c) := by
  refine ⟨rfl, ?_⟩
  intro k
  simpa using proximal_point_operator_mem g c (proximal_point_method g x0 c k)

end

end
