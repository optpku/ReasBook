/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Data.NNReal.Defs
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_25

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {Source : Type u} {Link : Type v}

/- Algorithm 8.16 is `source-facing`: the textbook specifies the NUM dual projected subgradient
iteration itself, with explicit per-source scalar argmax updates and the coordinatewise positive
part update for link prices. The existing owner abstraction for the induced link load is already
available as `network_link_load` from Definition 8.25, so the new public API keeps only the
source-rate objective, the one-step link-price update, the recursive price sequence, and the
derived source-rate iterate. The argmax condition in step (A) is recorded separately by an
admissibility predicate on the source-rate selection rule rather than being hidden behind a
noncanonical choice operator. -/

/-- The scalar objective maximized by source `s` in the NUM dual update, namely
`x_s ↦ u_s(x_s) - (∑_{ℓ ∈ L(s)} λ_ℓ) x_s`. -/
def network_utility_source_rate_objective
    (u : Source → ℝ → ℝ) (linksUsedBySource : Source → Finset Link)
    (lam : Link → NNReal) (s : Source) : ℝ → ℝ :=
  fun x ↦ u s x - Finset.sum (linksUsedBySource s) (fun ℓ ↦ (lam ℓ : ℝ)) * x

-- Proof sketch: unfold `network_utility_source_rate_objective`; evaluation at `x` is exactly the
-- utility term `u s x` minus the route-price sum `∑ ℓ ∈ L(s), λ_ℓ` multiplied by `x`.
/-- Evaluating `network_utility_source_rate_objective u linksUsedBySource lam s` at `x` gives the
NUM source-rate objective `u_s(x) - (∑_{ℓ ∈ L(s)} λ_ℓ) x`. -/
@[simp] theorem network_utility_source_rate_objective_apply
    (u : Source → ℝ → ℝ) (linksUsedBySource : Source → Finset Link)
    (lam : Link → NNReal) (s : Source) (x : ℝ) :
    network_utility_source_rate_objective u linksUsedBySource lam s x =
      u s x - Finset.sum (linksUsedBySource s) (fun ℓ ↦ (lam ℓ : ℝ)) * x := by
  rfl

/-- A source-rate selection rule is admissible for the NUM dual projected subgradient method when
every stepsize is strictly positive and each selected source rate `x_s^k` attains the argmax from
step (A) on the prescribed set `I_s`. -/
def network_utility_dual_projected_subgradient_method_is_admissible
    (u : Source → ℝ → ℝ) (linksUsedBySource : Source → Finset Link)
    (I : Source → Set ℝ) (α : ℕ → ℝ) (xSel : (Link → NNReal) → Source → ℝ) : Prop :=
  (∀ k : ℕ, 0 < α k) ∧
    ∀ lam : Link → NNReal, ∀ s : Source,
      IsMaxOn (network_utility_source_rate_objective u linksUsedBySource lam s) (I s) (xSel lam s)

section

variable [Fintype Source] [DecidableEq Link]

/-- The one-step link-price update
`λ_ℓ^+ = [λ_ℓ + α (∑_{s ∈ S(ℓ)} x_s - c_ℓ)]_+` from the NUM dual projected subgradient method. -/
def network_utility_link_price_update
    (linksUsedBySource : Source → Finset Link) (c : Link → ℝ)
    (α : ℝ) (lam : Link → NNReal) (x : Source → ℝ) : Link → NNReal :=
  fun ℓ ↦ Real.toNNReal ((lam ℓ : ℝ) + α * (network_link_load linksUsedBySource x ℓ - c ℓ))

-- Proof sketch: unfold `network_utility_link_price_update`; the `ℓ`-th coordinate is the
-- coordinatewise positive part of the current price plus the stepsize times the excess load
-- `∑_{s ∈ S(ℓ)} x_s - c_ℓ`.
/-- Evaluating `network_utility_link_price_update linksUsedBySource c α lam x` at `ℓ` returns the
positive-part link-price update for that link. -/
@[simp] theorem network_utility_link_price_update_apply
    (linksUsedBySource : Source → Finset Link) (c : Link → ℝ)
    (α : ℝ) (lam : Link → NNReal) (x : Source → ℝ) (ℓ : Link) :
    network_utility_link_price_update linksUsedBySource c α lam x ℓ =
      Real.toNNReal ((lam ℓ : ℝ) + α * (network_link_load linksUsedBySource x ℓ - c ℓ)) := by
  rfl

/-- Algorithm 8.16: given a route-incidence map `linksUsedBySource`, link capacities `c`,
stepsizes `α_k`, and a rule `xSel` selecting for each link-price vector `λ^k` the corresponding
source-rate update from step (A), the NUM dual projected subgradient method starts from
`λ^0 = 0` and recursively generates the link-price sequence by
`λ^{k+1}_ℓ = [λ^k_ℓ + α_k (∑_{s ∈ S(ℓ)} x_s^k - c_ℓ)]_+`. -/
def network_utility_dual_projected_subgradient_method
    (linksUsedBySource : Source → Finset Link) (c : Link → ℝ)
    (α : ℕ → ℝ) (xSel : (Link → NNReal) → Source → ℝ) : ℕ → Link → NNReal
  | 0 => 0
  | k + 1 =>
      let lamk := network_utility_dual_projected_subgradient_method linksUsedBySource c α xSel k
      let xk := xSel lamk
      network_utility_link_price_update linksUsedBySource c (α k) lamk xk

/-- The source-rate vector `x^k` selected from step (A) at the current link-price iterate `λ^k`.
-/
def network_utility_dual_projected_subgradient_source_rate_iterate
    (linksUsedBySource : Source → Finset Link) (c : Link → ℝ)
    (α : ℕ → ℝ) (xSel : (Link → NNReal) → Source → ℝ) (k : ℕ) : Source → ℝ :=
  xSel (network_utility_dual_projected_subgradient_method linksUsedBySource c α xSel k)

section

variable (linksUsedBySource : Source → Finset Link) (c : Link → ℝ)
variable (α : ℕ → ℝ) (xSel : (Link → NNReal) → Source → ℝ)

local notation "lam[" k "]" =>
  network_utility_dual_projected_subgradient_method linksUsedBySource c α xSel k

local notation "x[" k "]" =>
  network_utility_dual_projected_subgradient_source_rate_iterate linksUsedBySource c α xSel k

-- Proof sketch: unfold the recursive definition of
-- `network_utility_dual_projected_subgradient_method` at `0`.
/-- The NUM dual projected-subgradient link-price sequence starts from the zero multiplier vector.
-/
@[simp] theorem network_utility_dual_projected_subgradient_method_zero :
    lam[0] = 0 := by
  rfl

-- Proof sketch: unfold `network_utility_dual_projected_subgradient_source_rate_iterate`; by
-- definition the source-rate iterate `x^k` is obtained by applying `xSel` to the current
-- link-price iterate `λ^k`.
/-- The source-rate iterate `x^k` is obtained by applying the selection rule `xSel` to the
current link-price iterate `λ^k`. -/
@[simp] theorem network_utility_dual_projected_subgradient_source_rate_iterate_eq (k : ℕ) :
    x[k] = xSel lam[k] := by
  rfl

-- Proof sketch: unfold the recursive clause of
-- `network_utility_dual_projected_subgradient_method` at `k + 1`; it is definitionally the
-- link-price update applied to the current pair `(λ^k, x^k)`.
/-- One step of the NUM dual projected subgradient method applies the link-price update from
Algorithm 8.16 to the current link-price iterate `λ^k` and source-rate iterate `x^k`. -/
theorem network_utility_dual_projected_subgradient_method_succ (k : ℕ) :
    lam[k + 1] =
      network_utility_link_price_update linksUsedBySource c (α k) lam[k] x[k] := by
  rfl

-- Proof sketch: unfold `network_utility_dual_projected_subgradient_method_is_admissible` and
-- specialize the argmax clause to the current link-price iterate `λ^k` and source `s`.
/-- Under the admissibility condition, the selected source-rate component `x_s^k` attains the
argmax from step (A) of Algorithm 8.16 on the set `I_s`. -/
theorem network_utility_dual_projected_subgradient_source_rate_iterate_isMaxOn
    {u : Source → ℝ → ℝ} {I : Source → Set ℝ}
    (h : network_utility_dual_projected_subgradient_method_is_admissible
      u linksUsedBySource I α xSel)
    (k : ℕ) (s : Source) :
    IsMaxOn (network_utility_source_rate_objective u linksUsedBySource lam[k] s) (I s) (x[k] s) :=
  h.2 _ _

end

end

section

variable (linksUsedBySource : Source → Finset Link)
variable (α : ℕ → ℝ) (xSel : (Link → NNReal) → Source → ℝ)

-- Proof sketch: unfold `network_utility_dual_projected_subgradient_method_is_admissible` and
-- read off the positivity clause for the stepsize sequence.
/-- Under the admissibility condition, every stepsize in the NUM dual projected subgradient
method is strictly positive. -/
theorem network_utility_dual_projected_subgradient_method_stepsize_pos
    {u : Source → ℝ → ℝ} {I : Source → Set ℝ}
    (h : network_utility_dual_projected_subgradient_method_is_admissible
      u linksUsedBySource I α xSel)
    (k : ℕ) :
    0 < α k := by
  exact h.1 k

end

end
