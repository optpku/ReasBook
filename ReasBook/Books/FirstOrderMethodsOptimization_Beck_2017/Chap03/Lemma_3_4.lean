/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {m p : ℕ}

local notation "inequalitySpace" => EuclideanSpace ℝ (Fin m)
local notation "equalitySpace" => EuclideanSpace ℝ (Fin p)
local notation "perturbationSpace" =>
  inequalitySpace × equalitySpace

/- Lemma 3.4 is `source-facing` in the perturbation-value-function API. Its
`core/canonical` owner declarations are the Chapter 2 convexity predicate
`is_convex_function` and the partial-minimization theorem
`partial_infimum_is_convex_function`. This file keeps only the source-facing
feasible-set and value-function constructions, with the membership/evaluation
facts exposed as derived simp lemmas. -/

/-- The feasible set for the perturbation parameter `(u, t)` consists of the points of `X`
satisfying the coordinatewise inequality constraints `g i x ≤ u i` and the affine equality
constraint `A x + b = t`. -/
def value_function_feasible_set (X : Set E) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    (u : inequalitySpace) (t : equalitySpace) : Set E :=
  {x | x ∈ X ∧ (∀ i : Fin m, g i x ≤ (u i : EReal)) ∧ A x + b = t}

-- Proof sketch: unfold `value_function_feasible_set`; membership is exactly the conjunction of
-- belonging to `X`, satisfying each scalar inequality constraint, and solving the affine equality
-- constraint.
/-- A point lies in the perturbation feasible set exactly when it belongs to `X`, satisfies every
inequality constraint, and meets the affine equality constraint. -/
@[simp] theorem mem_value_function_feasible_set (X : Set E) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    (u : inequalitySpace) (t : equalitySpace) (x : E) :
    x ∈ value_function_feasible_set X g A b u t ↔
      x ∈ X ∧ (∀ i : Fin m, g i x ≤ (u i : EReal)) ∧ A x + b = t :=
  Iff.rfl

/-- The perturbation value function assigns to `(u, t)` the infimum of `f` over the feasible set
cut out by the perturbation constraints. -/
def value_function (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace) :
    perturbationSpace → EReal :=
  Function.uncurry fun u t ↦ sInf (f '' value_function_feasible_set X g A b u t)

-- Proof sketch: unfold `value_function`; evaluation at `(u, t)` is definitionally the infimum of
-- the image of `f` on `value_function_feasible_set X g A b u t`.
/-- Evaluating the perturbation value function at `(u, t)` gives the infimum of `f` over the
corresponding feasible set. -/
@[simp] theorem value_function_apply (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    (u : inequalitySpace) (t : equalitySpace) :
    value_function X f g A b (u, t) =
      sInf (f '' value_function_feasible_set X g A b u t) :=
  rfl

-- Proof sketch: if `∀ i, u i ≤ w i`, every point feasible for `u` is also feasible for `w`,
-- because the only changing conditions are the coordinatewise bounds `g i x ≤ u i`. Membership in
-- `X` and the affine equality constraint are unchanged.
/-- Relaxing the inequality perturbation coordinates enlarges the perturbation feasible set. -/
theorem value_function_feasible_set_mono_u (X : Set E) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    {u w : inequalitySpace} {t : equalitySpace} (huw : ∀ i : Fin m, u i ≤ w i) :
    value_function_feasible_set X g A b u t ⊆ value_function_feasible_set X g A b w t := by
  intro x hx
  rcases (mem_value_function_feasible_set X g A b u t x).1 hx with ⟨hxX, hxg, hxt⟩
  exact (mem_value_function_feasible_set X g A b w t x).2
    ⟨hxX, fun i ↦ (hxg i).trans <| by exact_mod_cast huw i, hxt⟩

-- Proof sketch: `value_function_feasible_set_mono_u` shows the feasible set for `u` sits inside
-- the feasible set for `w` whenever `∀ i, u i ≤ w i`. Taking infima of `f` over these nested
-- feasible sets yields antitonicity in the inequality perturbation parameter.
/-- For fixed equality perturbation `t`, the perturbation value function is antitone in the
inequality perturbation parameter. -/
theorem value_function_antitone_u (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    {u w : inequalitySpace} {t : equalitySpace} (huw : ∀ i : Fin m, u i ≤ w i) :
    value_function X f g A b (u, t) ≥ value_function X f g A b (w, t) := by
  rw [value_function_apply, value_function_apply]
  refine sInf_le_sInf ?_
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, value_function_feasible_set_mono_u X g A b huw hx, rfl⟩

-- API check: Chapter 2 uses `IsProperExtendedRealFunction` as the canonical properness predicate
-- for extended-real-valued functions, so the source hypothesis on the value function is stated
-- with that owner here.
-- Proof sketch: if `value_function X f g A b (u, t) < ⊤`, then the feasible set for `(u, t)`
-- cannot be empty, because `sInf (f '' ∅) = ⊤`. Any feasible point for any perturbation slice lies
-- in `X`, so every effective-domain point of the value function certifies `X.Nonempty`.
/-- Any effective-domain point of the perturbation value function forces the base set `X` to be
nonempty. -/
theorem nonempty_of_mem_effective_domain_value_function
    (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    {u : inequalitySpace} {t : equalitySpace}
    (huvt : (u, t) ∈ effective_domain (value_function X f g A b)) :
    X.Nonempty := by
  rw [mem_effective_domain, value_function_apply] at huvt
  by_contra hX
  have hX_empty : X = ∅ := Set.not_nonempty_iff_eq_empty.mp hX
  have hfeasible_empty : value_function_feasible_set X g A b u t = ∅ := by
    ext x
    simp [value_function_feasible_set, hX_empty]
  simp [hfeasible_empty] at huvt

-- Proof sketch: properness provides a point in the effective domain of `value_function X f g A b`;
-- the previous lemma then shows that this finite perturbation slice contains a feasible point, so
-- `X` is automatically nonempty.
/-- Properness of the perturbation value function implies that the underlying constraint set `X`
is nonempty. -/
theorem value_function_nonempty_of_proper
    (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    (hv_proper : IsProperExtendedRealFunction (value_function X f g A b)) :
    X.Nonempty := by
  obtain ⟨⟨u, t⟩, huvt⟩ := hv_proper.effective_domain_nonempty
  exact nonempty_of_mem_effective_domain_value_function X f g A b huvt

/-- Helper for Lemma 3.4: membership in each perturbation feasible slice is classically
decidable. -/
local instance valueFunctionFeasibleSetMemDecidable
    (X : Set E) (g : Fin m → E → EReal) (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    (u : inequalitySpace) (t : equalitySpace) :
    DecidablePred (fun x : E ↦ x ∈ value_function_feasible_set X g A b u t) :=
  Classical.decPred _

/-- Helper for Lemma 3.4: the joint feasible-if objective equals `f x` on feasible perturbation
triples `((u, t), x)` and `⊤` outside the perturbation feasible set. -/
def jointFeasibleObjective (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace) :
    perturbationSpace × E → EReal :=
  fun z ↦
    if z.2 ∈ value_function_feasible_set X g A b z.1.1 z.1.2 then
      f z.2
    else
      ⊤

-- Proof sketch: split on feasibility. On the feasible branch the joint objective is `f x`, while
-- on the infeasible branch the epigraph inequality is impossible because `⊤ ≤ (r : EReal)` fails.
/-- Helper for Lemma 3.4: the real-epigraph condition for `jointFeasibleObjective` is exactly
feasibility together with the epigraph condition for `f`. -/
theorem mem_jointFeasibleObjective_epigraph_iff
    (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    (u : inequalitySpace) (t : equalitySpace) (x : E) (r : ℝ) :
    jointFeasibleObjective X f g A b ((u, t), x) ≤ (r : EReal) ↔
      x ∈ value_function_feasible_set X g A b u t ∧ f x ≤ (r : EReal) := by
  -- Split on feasibility to remove the branch returning `⊤`.
  by_cases hx : x ∈ value_function_feasible_set X g A b u t
  · simp [jointFeasibleObjective, hx]
  · simp [jointFeasibleObjective, hx]

-- Proof sketch: expand `A (α • x₁ + β • x₂)` linearly and rewrite the free `b` term as
-- `(α + β) • b`; the hypothesis `α + β = 1` then packages the result into the weighted endpoint
-- constraints.
/-- Helper for Lemma 3.4: affine equality constraints are preserved by convex combinations of
feasible points and perturbations. -/
theorem affineConstraint_combo_eq
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    {α β : ℝ} (hαβ : α + β = 1)
    {x₁ x₂ : E} {t₁ t₂ : equalitySpace}
    (hx₁ : A x₁ + b = t₁) (hx₂ : A x₂ + b = t₂) :
    A (α • x₁ + β • x₂) + b = α • t₁ + β • t₂ := by
  -- Rewrite the affine constraint at the convex combination into the weighted endpoint equalities.
  calc
    A (α • x₁ + β • x₂) + b
        = A (α • x₁ + β • x₂) + (α + β) • b := by
            simp [hαβ]
    _ = α • (A x₁ + b) + β • (A x₂ + b) := by
          simp [LinearMap.map_add, smul_add, add_smul, add_assoc, add_left_comm, add_comm]
    _ = α • t₁ + β • t₂ := by rw [hx₁, hx₂]

-- Proof sketch: keep the convexity argument at the source-facing feasible-set level. Convexity of
-- `X` handles set membership, the epigraph convexity of each `g i` handles the coordinatewise
-- inequalities, and `affineConstraint_combo_eq` transports the affine equality constraint.
/-- Helper for Lemma 3.4: the perturbation feasible set is closed under simultaneous convex
combination of the primal point and perturbation parameters. -/
theorem combo_mem_valueFunctionFeasibleSet
    (X : Set E) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    (hg_convex : ∀ i : Fin m, is_convex_function (g i))
    (hX_convex : Convex ℝ X)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    {u₁ u₂ : inequalitySpace} {t₁ t₂ : equalitySpace} {x₁ x₂ : E}
    (hx₁ : x₁ ∈ value_function_feasible_set X g A b u₁ t₁)
    (hx₂ : x₂ ∈ value_function_feasible_set X g A b u₂ t₂) :
    α • x₁ + β • x₂ ∈
      value_function_feasible_set X g A b (α • u₁ + β • u₂) (α • t₁ + β • t₂) := by
  rcases (mem_value_function_feasible_set X g A b u₁ t₁ x₁).1 hx₁ with ⟨hx₁X, hx₁g, hx₁eq⟩
  rcases (mem_value_function_feasible_set X g A b u₂ t₂ x₂).1 hx₂ with ⟨hx₂X, hx₂g, hx₂eq⟩
  refine (mem_value_function_feasible_set X g A b (α • u₁ + β • u₂) (α • t₁ + β • t₂)
    (α • x₁ + β • x₂)).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · -- Convexity of `X` keeps the primal point inside the base feasible region.
    exact hX_convex hx₁X hx₂X hα hβ hαβ
  · -- For each coordinate, convexity of the epigraph of `g i` transports the inequality bound.
    intro i
    have hgi_epigraph : Convex ℝ {p : E × ℝ | g i p.1 ≤ (p.2 : EReal)} :=
      (is_convex_function_iff_convex_real_epigraph (g i)).mp (hg_convex i)
    have hx₁_mem : (x₁, u₁ i) ∈ {p : E × ℝ | g i p.1 ≤ (p.2 : EReal)} := hx₁g i
    have hx₂_mem : (x₂, u₂ i) ∈ {p : E × ℝ | g i p.1 ≤ (p.2 : EReal)} := hx₂g i
    simpa [Prod.smul_mk, Prod.mk_add_mk] using
      (convex_iff_add_mem.mp hgi_epigraph) hx₁_mem hx₂_mem hα hβ hαβ
  · -- The affine equality constraint is linear in the primal point and perturbation slice.
    exact affineConstraint_combo_eq A b hαβ hx₁eq hx₂eq

-- Proof sketch: rewrite the real epigraph of the feasible-if objective using
-- `mem_jointFeasibleObjective_epigraph_iff`, then combine the feasible-set closure lemma with the
-- epigraph convexity of `f`.
/-- Helper for Lemma 3.4: the feasible-if joint objective on `perturbationSpace × E` is convex. -/
theorem jointFeasibleObjective_isConvex
    (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    (hf_convex : is_convex_function f) (hg_convex : ∀ i : Fin m, is_convex_function (g i))
    (hX_convex : Convex ℝ X) :
    is_convex_function (jointFeasibleObjective X f g A b) := by
  rw [is_convex_function_iff_convex_real_epigraph]
  rw [convex_iff_add_mem]
  intro p₁ hp₁ p₂ hp₂ α β hα hβ hαβ
  rcases p₁ with ⟨⟨⟨u₁, t₁⟩, x₁⟩, r₁⟩
  rcases p₂ with ⟨⟨⟨u₂, t₂⟩, x₂⟩, r₂⟩
  have hp₁' := (mem_jointFeasibleObjective_epigraph_iff X f g A b u₁ t₁ x₁ r₁).1 hp₁
  have hp₂' := (mem_jointFeasibleObjective_epigraph_iff X f g A b u₂ t₂ x₂ r₂).1 hp₂
  rcases hp₁' with ⟨hx₁_feasible, hx₁_epi⟩
  rcases hp₂' with ⟨hx₂_feasible, hx₂_epi⟩
  -- First combine the perturbation feasibility data at the level of the source-facing constraints.
  have hfeasible :
      α • x₁ + β • x₂ ∈
        value_function_feasible_set X g A b (α • u₁ + β • u₂) (α • t₁ + β • t₂) := by
    exact combo_mem_valueFunctionFeasibleSet X g A b hg_convex hX_convex hα hβ hαβ
      hx₁_feasible hx₂_feasible
  have hf_epigraph : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} :=
    (is_convex_function_iff_convex_real_epigraph f).mp hf_convex
  -- Then convexity of the epigraph of `f` controls the objective value at that combined point.
  have hvalue :
      f (α • x₁ + β • x₂) ≤ ((α * r₁ + β * r₂ : ℝ) : EReal) := by
    have hx₁_mem : (x₁, r₁) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := hx₁_epi
    have hx₂_mem : (x₂, r₂) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := hx₂_epi
    simpa [Prod.smul_mk, Prod.mk_add_mk] using
      (convex_iff_add_mem.mp hf_epigraph) hx₁_mem hx₂_mem hα hβ hαβ
  have hcombo :
      jointFeasibleObjective X f g A b
          (((α • u₁ + β • u₂, α • t₁ + β • t₂), α • x₁ + β • x₂))
        ≤ ((α * r₁ + β * r₂ : ℝ) : EReal) := by
    exact (mem_jointFeasibleObjective_epigraph_iff X f g A b
      (α • u₁ + β • u₂) (α • t₁ + β • t₂) (α • x₁ + β • x₂)
      (α * r₁ + β * r₂)).2 ⟨hfeasible, hvalue⟩
  simpa [Prod.smul_mk, Prod.mk_add_mk] using hcombo

-- Proof sketch: compare the source-facing value-function infimum with the partial-infimum range
-- of `jointFeasibleObjective`. Feasible points contribute the original `f`-values, while every
-- infeasible point contributes only `⊤`, which does not lower the infimum.
/-- Helper for Lemma 3.4: the perturbation value function is the partial infimum of
`jointFeasibleObjective` over the primal variable. -/
@[simp] theorem valueFunction_eq_partialInf_jointFeasibleObjective
    (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    (u : inequalitySpace) (t : equalitySpace) :
    value_function X f g A b (u, t) =
      sInf (Set.range fun x : E ↦ jointFeasibleObjective X f g A b ((u, t), x)) := by
  rw [value_function_apply]
  apply le_antisymm
  · -- Every point in the joint range is above the original infimum over feasible points.
    refine le_sInf ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    by_cases hx : x ∈ value_function_feasible_set X g A b u t
    · simpa [jointFeasibleObjective, hx] using
        (sInf_le (by exact ⟨x, hx, rfl⟩) :
          sInf (f '' value_function_feasible_set X g A b u t) ≤ f x)
    · simp [jointFeasibleObjective, hx]
  · -- Each feasible objective value already appears in the joint partial-infimum range.
    refine le_sInf ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa [jointFeasibleObjective, hx] using
      (sInf_le (Set.mem_range_self x) :
        sInf (Set.range fun x : E ↦ jointFeasibleObjective X f g A b ((u, t), x)) ≤
          jointFeasibleObjective X f g A b ((u, t), x))

-- Proof sketch: view `value_function X f g A b` as the partial infimum in the `E`-variable of the
-- jointly convex constrained objective on `E × (ℝ^m × ℝ^p)` that equals `f x` on the convex set of
-- triples `(x, u, t)` with `x ∈ X`, `g i x ≤ u i`, and `A x + b = t`, and equals `⊤` outside that
-- set. Convexity of `X`, of `f`, and of each `g i`, together with linearity of `A`, gives
-- convexity of that owner objective. This is exactly the Chapter 2 partial-infimum consequence,
-- so the refined source-facing statement keeps only the convexity hypotheses and does not impose
-- extra properness or nonemptiness assumptions.
/-- Lemma 3.4: if `f` and all constraint functions `g i` are convex and `X` is convex, then the
perturbation value function is convex on `ℝ^m × ℝ^p`. -/
theorem value_function_is_convex (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] equalitySpace) (b : equalitySpace)
    (hf_convex : is_convex_function f) (hg_convex : ∀ i : Fin m, is_convex_function (g i))
    (hX_convex : Convex ℝ X) :
    is_convex_function (value_function X f g A b) := by
  -- Route correction: instead of reproducing the source liminf argument, identify the value
  -- function as a partial infimum of a jointly convex feasible-if objective and invoke Theorem 2.7.
  have hJointConvex :
      is_convex_function (jointFeasibleObjective X f g A b) :=
    jointFeasibleObjective_isConvex X f g A b hf_convex hg_convex hX_convex
  have hPartial :
      is_convex_function
        (fun z : perturbationSpace ↦
          sInf (Set.range fun x : E ↦ jointFeasibleObjective X f g A b (z, x))) :=
    partial_infimum_is_convex_function hJointConvex
  have hPartialEq :
      (fun z : perturbationSpace ↦
        sInf (Set.range fun x : E ↦ jointFeasibleObjective X f g A b (z, x))) =
        value_function X f g A b := by
    funext z
    rcases z with ⟨u, t⟩
    symm
    exact valueFunction_eq_partialInf_jointFeasibleObjective X f g A b u t
  -- Rewrite the Chapter 2 partial infimum back to the source-facing value function.
  simpa [hPartialEq] using hPartial

end
