/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Filter.Extr

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

section

variable {Source : Type u} {Link : Type v}
variable [Fintype Source] [DecidableEq Link]

/- Definition 8.25 is `source-facing`: the textbook introduces a finite-source, finite-link
network utility maximization problem. Domain sampling against earlier Chapter 8 items shows that
the canonical owner for the optimization statement itself is mathlib's `IsMaxOn`; the genuinely
new local objects are the total-utility objective and the feasible rate set cut out by the
capacity and box constraints. The link-user sets `S(ℓ)` are derivable from the primitive
per-source route data `linksUsedBySource`, so they are not packaged as a second public owner. -/

/-- The total utility of a source-rate vector `x`, obtained by summing the utilities
`u_s (x_s)` over all sources. -/
def network_utility_objective (u : Source → ℝ → ℝ) : (Source → ℝ) → ℝ :=
  fun x ↦ ∑ s : Source, u s (x s)

-- Proof sketch: unfold `network_utility_objective`; it is definitionally the finite sum of the
-- source utilities evaluated at the corresponding coordinates of `x`.
/-- Evaluating `network_utility_objective u` at `x` gives the finite sum
`∑ s, u s (x s)`. -/
@[simp] theorem network_utility_objective_apply
    (u : Source → ℝ → ℝ) (x : Source → ℝ) :
    network_utility_objective u x = ∑ s : Source, u s (x s) := by
  -- Unfolding the objective exposes exactly the textbook sum of source utilities.
  rfl

/-- The total load induced on a link `ℓ` by the source-rate vector `x`, obtained by summing the
rates of the sources whose routes use `ℓ`. -/
def network_link_load
    (linksUsedBySource : Source → Finset Link) (x : Source → ℝ) (ℓ : Link) : ℝ :=
  ∑ s : Source, if ℓ ∈ linksUsedBySource s then x s else 0

-- Proof sketch: unfold `network_link_load`; it is definitionally the finite sum over all sources
-- with the indicator term selecting exactly those sources whose route contains `ℓ`.
/-- Evaluating `network_link_load linksUsedBySource x` at `ℓ` gives the sum of the rates
`x_s` over the sources whose routes use `ℓ`. -/
@[simp] theorem network_link_load_eq_sum
    (linksUsedBySource : Source → Finset Link) (x : Source → ℝ) (ℓ : Link) :
    network_link_load linksUsedBySource x ℓ =
      ∑ s : Source, if ℓ ∈ linksUsedBySource s then x s else 0 := by
  -- Unfolding the link load exposes the indicator-weighted sum over all sources.
  rfl

/-- Definition 8.25: the feasible rate vectors for the network utility maximization problem
`(8.91)` are those satisfying every link-capacity constraint
`∑_{s ∈ S(ℓ)} x_s ≤ c_ℓ` and every box constraint `x_s ∈ [0, M_s]`. -/
def network_utility_maximization_feasible_set
    (linksUsedBySource : Source → Finset Link) (c : Link → ℝ) (M : Source → ℝ) :
    Set (Source → ℝ) :=
  {x |
    (∀ ℓ : Link, network_link_load linksUsedBySource x ℓ ≤ c ℓ) ∧
      ∀ s : Source, x s ∈ Set.Icc 0 (M s)}

-- Proof sketch: unfold `network_utility_maximization_feasible_set`; membership is exactly the
-- conjunction of the link-capacity constraints and the interval constraints `x_s ∈ [0, M_s]`.
/-- Membership in `network_utility_maximization_feasible_set linksUsedBySource c M` means that
every link load is bounded by capacity and every source rate lies in its interval `[0, M_s]`. -/
@[simp] theorem mem_network_utility_maximization_feasible_set
    {linksUsedBySource : Source → Finset Link} {c : Link → ℝ} {M : Source → ℝ}
    {x : Source → ℝ} :
    x ∈ network_utility_maximization_feasible_set linksUsedBySource c M ↔
      (∀ ℓ : Link, network_link_load linksUsedBySource x ℓ ≤ c ℓ) ∧
        ∀ s : Source, x s ∈ Set.Icc 0 (M s) := by
  -- Membership is definitionally the conjunction of all capacity and box constraints.
  rfl

-- Proof sketch: rewrite `IsMaxOn` using `isMaxOn_iff` and keep the maximizer's own feasibility
-- explicit, since `IsMaxOn` alone only compares against feasible points and does not imply
-- membership of `x` in the feasible set.
/-- Definition 8.25, source-facing optimizer form: a rate vector `x` solves the network utility
maximization problem exactly when it is feasible and every other feasible rate vector has no
larger total utility. -/
theorem mem_and_isMaxOn_network_utility_maximization_feasible_set_iff
    {u : Source → ℝ → ℝ} {linksUsedBySource : Source → Finset Link}
    {c : Link → ℝ} {M : Source → ℝ} {x : Source → ℝ} :
    x ∈ network_utility_maximization_feasible_set linksUsedBySource c M ∧
      IsMaxOn
        (network_utility_objective u)
        (network_utility_maximization_feasible_set linksUsedBySource c M)
        x ↔
      (∀ ℓ : Link, network_link_load linksUsedBySource x ℓ ≤ c ℓ) ∧
        (∀ s : Source, x s ∈ Set.Icc 0 (M s)) ∧
        ∀ y : Source → ℝ,
          (∀ ℓ : Link, network_link_load linksUsedBySource y ℓ ≤ c ℓ) →
            (∀ s : Source, y s ∈ Set.Icc 0 (M s)) →
              network_utility_objective u y ≤ network_utility_objective u x := by
  constructor
  · rintro ⟨hx, hmax⟩
    rw [isMaxOn_iff] at hmax
    refine ⟨hx.1, hx.2, ?_⟩
    -- Any feasible comparison point `y` lies in the same feasible set, so `hmax` applies.
    intro y hy_capacity hy_box
    exact hmax y ⟨hy_capacity, hy_box⟩
  · rintro ⟨hx_capacity, hx_box, hopt⟩
    refine ⟨⟨hx_capacity, hx_box⟩, ?_⟩
    rw [isMaxOn_iff]
    -- Repackaging feasibility as set membership reduces the comparison step to `hopt`.
    intro y hy
    exact hopt y hy.1 hy.2

end
