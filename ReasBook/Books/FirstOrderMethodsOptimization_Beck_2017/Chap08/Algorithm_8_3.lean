/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 8.3 is `source-facing` in the constrained first-order API. The canonical owner data
for the projection step is the chapter map `metricProjection`, and the canonical owner for a chosen
Euclidean subgradient is `euclideanSubdifferentialAt`. Since the iterate is projected back onto the
feasible set at every step, the recursive sequence is most naturally valued in the subtype `C`. -/

/-- Algorithm 8.3: for a nonempty closed convex feasible set `C`, a feasible initial point `x0`,
stepsizes `t_k`, and a rule `g` selecting a subgradient direction at each current feasible
iterate, the projected subgradient method generates the sequence
`x^{k+1} = P_C (x^k - t_k g_k(x^k))`. -/
def projected_subgradient_method (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C) : ℕ → C
  | 0 => x0
  | k + 1 =>
      -- Route correction: the chapter-level metric projection API is parameterized by completeness,
      -- so the closed feasible set supplies the needed input through `hC_closed`.
      let xk := projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k
      metricProjection C hC_nonempty hC_closed hC_convex
        ((xk : E) - t k • g k xk)

/-- The ambient-space iterate sequence obtained by coercing the feasible projected-subgradient
iterates from `C` to `E`. This is the canonical bridge for objective values and norm estimates,
which are naturally stated in the ambient space. -/
abbrev projected_subgradient_method_iterate (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C) : ℕ → E :=
  fun k ↦ projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k

/-- A direction-selection rule is admissible for the projected subgradient method on `f` when, at
each iterate, the selected direction belongs to the Euclidean subdifferential of `f` at the
current iterate and the current stepsize is strictly positive. -/
def projected_subgradient_method_is_admissible
    (f : E → ℝ) (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C) : Prop :=
  ∀ k,
    g k (projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k) ∈
        euclideanSubdifferentialAt f
          (projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k) ∧
      0 < t k

-- Proof sketch: unfold the recursive definition of `projected_subgradient_method` at `0`.
/-- The projected-subgradient sequence starts at the prescribed feasible initial point. -/
theorem projected_subgradient_method_zero (C : Set E) (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C) :
    projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 0 = x0 := by
  -- The base case is exactly the `0` branch of the recursive definition.
  rfl

-- Proof sketch: unfold the recursive definition of `projected_subgradient_method` at `k + 1`.
/-- One step of the projected subgradient method applies the metric projection onto `C` to the
current iterate minus the current stepsize times the selected subgradient direction. -/
theorem projected_subgradient_method_succ (C : Set E) (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)
    (k : ℕ) :
    projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 (k + 1) =
      metricProjection C hC_nonempty hC_closed hC_convex
        ((projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k : E) -
          t k • g k (projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k)) :=
  by
    -- Unfolding one recursive step exposes the projected update rule verbatim.
    rfl

-- Proof sketch: unfold `projected_subgradient_method_iterate` at `0`; this is the ambient-space
-- coercion of `projected_subgradient_method_zero`.
/-- The ambient projected-subgradient iterate sequence starts at the prescribed initial point. -/
@[simp] theorem projected_subgradient_method_iterate_zero (C : Set E) (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C) :
    projected_subgradient_method_iterate C hC_nonempty hC_closed hC_convex g t x0 0 = x0 := by
  rfl

-- Proof sketch: unfold `projected_subgradient_method_iterate` at `k + 1`; this is the ambient
-- version of `projected_subgradient_method_succ`.
/-- One step of the ambient projected-subgradient iterate sequence is the projected update in `E`.
-/
theorem projected_subgradient_method_iterate_succ (C : Set E) (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)
    (k : ℕ) :
    projected_subgradient_method_iterate C hC_nonempty hC_closed hC_convex g t x0 (k + 1) =
      metricProjection C hC_nonempty hC_closed hC_convex
        (projected_subgradient_method_iterate C hC_nonempty hC_closed hC_convex g t x0 k -
          t k • g k (projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k)) :=
  rfl

-- Proof sketch: unfold `projected_subgradient_method_is_admissible` and specialize its defining
-- condition at the index `k`.
/-- Under the admissibility condition, the selected direction at iteration `k` is a Euclidean
subgradient of `f` at the current projected iterate. -/
theorem projected_subgradient_method_subgradient_mem
    {f : E → ℝ} {C : Set E} {hC_nonempty : C.Nonempty} {hC_closed : IsClosed C}
    {hC_convex : Convex ℝ C} {g : ℕ → C → E} {t : ℕ → ℝ} {x0 : C}
    (h : projected_subgradient_method_is_admissible f C hC_nonempty hC_closed hC_convex g t x0)
    (k : ℕ) :
    g k (projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k) ∈
      euclideanSubdifferentialAt f
        (projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k) := by
  -- The admissibility predicate stores subgradient membership as its first component.
  exact (h k).1

-- Proof sketch: unfold `projected_subgradient_method_is_admissible` and read off the positivity
-- clause at the index `k`.
/-- Under the admissibility condition, every stepsize in the projected subgradient method is
strictly positive. -/
theorem projected_subgradient_method_stepsize_pos
    {f : E → ℝ} {C : Set E} {hC_nonempty : C.Nonempty} {hC_closed : IsClosed C}
    {hC_convex : Convex ℝ C} {g : ℕ → C → E} {t : ℕ → ℝ} {x0 : C}
    (h : projected_subgradient_method_is_admissible f C hC_nonempty hC_closed hC_convex g t x0)
    (k : ℕ) :
    0 < t k := by
  -- The admissibility predicate stores strict stepsize positivity as its second component.
  exact (h k).2

end
