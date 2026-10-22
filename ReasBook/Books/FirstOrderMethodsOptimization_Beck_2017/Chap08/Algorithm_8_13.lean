/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 8.13 is `source-facing`: the textbook defines both the outer iterates `x^k` and the
inner stage points `x^{k,i}` obtained by cycling through the component functions. The canonical
owner for each update remains the chapter projection map `metricProjection`, while the
subgradient-membership and positive-stepsize clauses are separate admissibility conditions on the
chosen directions. Because the source names the inner iterates explicitly, the public API keeps
them visible instead of packaging them into an auxiliary wrapper. -/

/-- The inner iterate `x^{k,i}` of the incremental projected subgradient method is obtained by
starting from the outer iterate `x^k` and successively applying the projected updates for the
first `i` components, truncated at `m`. -/
def incremental_projected_subgradient_inner_iterate {m : ℕ} (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (t : ℕ → ℝ) (g : ℕ → C → Fin m → E) (k : ℕ) (x : C) (i : ℕ) : C :=
  Fin.foldl (min i m)
    (fun y j ↦
      -- Route correction: the chapter projection API is parameterized by completeness, and the
      -- closed feasible set provides that input through `hC_closed`.
      metricProjection C hC_nonempty hC_closed hC_convex
        ((y : E) - t k • g k y (Fin.castLE (Nat.min_le_right i m) j)))
    x

-- Proof sketch: unfold `incremental_projected_subgradient_inner_iterate`; since
-- `List.finRange (min 0 m)` is empty, the left fold returns the initial value `x`.
/-- Evaluating the incremental projected inner iterate at stage `0` returns the supplied outer
iterate. -/
theorem incremental_projected_subgradient_inner_iterate_zero {m : ℕ} (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (t : ℕ → ℝ) (g : ℕ → C → Fin m → E) (k : ℕ) (x : C) :
    incremental_projected_subgradient_inner_iterate C hC_nonempty hC_closed hC_convex t g k x 0 =
      x := by
  -- The truncated component count is `0`, so `Fin.foldl` returns the base point `x`.
  simpa [incremental_projected_subgradient_inner_iterate] using
    (Fin.foldl_zero
      (f := fun y j ↦
        metricProjection C hC_nonempty hC_closed hC_convex
          ((y : E) - t k • g k y (Fin.castLE (Nat.min_le_right 0 m) j)))
      x)

-- Proof sketch: for `i < m`, rewrite `min (i + 1) m = i + 1` and split the fold over
-- `List.finRange (i + 1)` into the prefix `List.finRange i` followed by the last index `i`. The
-- last fold step is precisely the displayed projected update with component `i`.
/-- Advancing from inner stage `i` to `i + 1` applies the metric projection onto `C` after
stepping along the chosen subgradient of the `i`-th component with stepsize `t_k`. -/
theorem incremental_projected_subgradient_inner_iterate_succ {m : ℕ} (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (t : ℕ → ℝ) (g : ℕ → C → Fin m → E) (k : ℕ) (x : C) {i : ℕ} (hi : i < m) :
    incremental_projected_subgradient_inner_iterate C hC_nonempty hC_closed hC_convex t g k x
        (i + 1) =
      metricProjection C hC_nonempty hC_closed hC_convex
        ((incremental_projected_subgradient_inner_iterate
            C hC_nonempty hC_closed hC_convex t g k x i : E) -
          t k •
            g k
              (incremental_projected_subgradient_inner_iterate
                C hC_nonempty hC_closed hC_convex t g k x i)
              ⟨i, hi⟩) := by
  have hsucc :
      incremental_projected_subgradient_inner_iterate
          C hC_nonempty hC_closed hC_convex t g k x (i + 1) =
        Fin.foldl (i + 1)
          (fun y j ↦
            metricProjection C hC_nonempty hC_closed hC_convex
              ((y : E) - t k • g k y (Fin.castLE (Nat.succ_le_of_lt hi) j)))
          x := by
    -- Replace the truncated count `min (i + 1) m` by `i + 1` using the bound `i < m`.
    simpa [incremental_projected_subgradient_inner_iterate] using
      congrArg (fun F => F x) <|
        (Fin.foldl_congr
          (w := Nat.min_eq_left (Nat.succ_le_of_lt hi))
          (f := fun y j ↦
            metricProjection C hC_nonempty hC_closed hC_convex
              ((y : E) - t k • g k y (Fin.castLE (Nat.min_le_right (i + 1) m) j))))
  have hprefix_base :
      incremental_projected_subgradient_inner_iterate
          C hC_nonempty hC_closed hC_convex t g k x i =
        Fin.foldl i
          (fun y j ↦
            metricProjection C hC_nonempty hC_closed hC_convex
              ((y : E) - t k • g k y (Fin.castLE (Nat.le_of_lt hi) j)))
          x := by
    -- The same truncation rewrite identifies stage `i` with the prefix fold over the first `i`
    -- component indices.
    simpa [incremental_projected_subgradient_inner_iterate] using
      congrArg (fun F => F x) <|
        (Fin.foldl_congr
          (w := Nat.min_eq_left (Nat.le_of_lt hi))
          (f := fun y j ↦
            metricProjection C hC_nonempty hC_closed hC_convex
              ((y : E) - t k • g k y (Fin.castLE (Nat.min_le_right i m) j))))
  have hprefix :
      Fin.foldl i
          (fun y j ↦
            metricProjection C hC_nonempty hC_closed hC_convex
              ((y : E) - t k • g k y (j.castSucc.castLE (Nat.succ_le_of_lt hi))))
          x =
        incremental_projected_subgradient_inner_iterate
          C hC_nonempty hC_closed hC_convex t g k x i := by
    -- The prefix fold in `Fin.foldl_succ_last` matches stage `i` after simplifying the casted
    -- component indices.
    calc
      Fin.foldl i
          (fun y j ↦
            metricProjection C hC_nonempty hC_closed hC_convex
              ((y : E) - t k • g k y (j.castSucc.castLE (Nat.succ_le_of_lt hi))))
          x =
        Fin.foldl i
          (fun y j ↦
            metricProjection C hC_nonempty hC_closed hC_convex
              ((y : E) - t k • g k y (Fin.castLE (Nat.le_of_lt hi) j)))
          x := by
        congr with y j
      _ =
        incremental_projected_subgradient_inner_iterate
          C hC_nonempty hC_closed hC_convex t g k x i := hprefix_base.symm
  -- Decompose the `(i + 1)`-stage fold into the prefix through stage `i - 1` and the last
  -- component `i`.
  rw [hsucc, Fin.foldl_succ_last, hprefix]
  -- The last index in the `(i + 1)`-fold is exactly the component `i`.
  rw [show Fin.castLE (Nat.succ_le_of_lt hi) (Fin.last i) = (⟨i, hi⟩ : Fin m) by rfl]

/-- Algorithm 8.13: for a nonempty closed convex feasible set `C`, a feasible initial point `x0`,
positive stepsizes `t_k`, and chosen component subgradients `g^{k,i}`, the incremental projected
subgradient method generates outer iterates `x^{k+1} = x^{k,m}` where
`x^{k,i+1} = P_C (x^{k,i} - t_k g^{k,i})` and `x^{k,0} = x^k`. -/
def incremental_projected_subgradient_method {m : ℕ} (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (t : ℕ → ℝ) (g : ℕ → C → Fin m → E) (x0 : C) : ℕ → C
  | 0 => x0
  | k + 1 =>
      let xk :=
        incremental_projected_subgradient_method C hC_nonempty hC_closed hC_convex t g x0 k
      incremental_projected_subgradient_inner_iterate
        C hC_nonempty hC_closed hC_convex t g k xk m

/-- A component-selection rule is admissible for the incremental projected subgradient method when
every stepsize is positive and each chosen direction at the `i`-th inner stage belongs to the
Euclidean subdifferential of the `i`-th summand at the current inner iterate. -/
def incremental_projected_subgradient_method_is_admissible {m : ℕ}
    (f : Fin m → E → ℝ) (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (t : ℕ → ℝ) (g : ℕ → C → Fin m → E) (x0 : C) : Prop :=
  (∀ k, 0 < t k) ∧
    ∀ k (i : Fin m),
      g k
          (incremental_projected_subgradient_inner_iterate
            C hC_nonempty hC_closed hC_convex t g k
            (incremental_projected_subgradient_method
              C hC_nonempty hC_closed hC_convex t g x0 k)
            i)
          i ∈
        euclideanSubdifferentialAt (f i)
          (incremental_projected_subgradient_inner_iterate
            C hC_nonempty hC_closed hC_convex t g k
            (incremental_projected_subgradient_method
              C hC_nonempty hC_closed hC_convex t g x0 k)
            i : E)

section

variable {m : ℕ}
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (t : ℕ → ℝ) (g : ℕ → C → Fin m → E) (x0 : C)

local notation "x[" k "]" =>
  incremental_projected_subgradient_method C hC_nonempty hC_closed hC_convex t g x0 k

local notation "x[" k "," i "]" =>
  incremental_projected_subgradient_inner_iterate C hC_nonempty hC_closed hC_convex t g k x[k] i

-- Proof sketch: unfold the recursive definition of `incremental_projected_subgradient_method` at
-- `0`.
/-- The incremental projected-subgradient sequence starts at the prescribed feasible initial
point. -/
@[simp] theorem incremental_projected_subgradient_method_zero :
    x[0] = x0 := by
  -- The base case is exactly the `0` branch of the recursive definition.
  rfl

-- Proof sketch: `x[k, 0]` is the stage-`0` inner iterate based at `x[k]`, so this is exactly
-- `incremental_projected_subgradient_inner_iterate_zero` applied to the outer iterate `x[k]`.
/-- At each outer iteration `k`, the initial inner stage `x^{k,0}` agrees with the current outer
iterate `x^k`. -/
theorem incremental_projected_subgradient_method_inner_zero (k : ℕ) :
    x[k, 0] = x[k] := by
  -- Specializing the generic stage-`0` identity to the base point `x[k]` gives the claim.
  simpa using
    (incremental_projected_subgradient_inner_iterate_zero
      C hC_nonempty hC_closed hC_convex t g k x[k])

-- Proof sketch: apply `incremental_projected_subgradient_inner_iterate_succ` to the base point
-- `x[k]`. This identifies the `(i + 1)`-st inner stage with one projected update from `x[k, i]`
-- using the component direction indexed by `i`.
/-- At each inner stage `i < m`, the next stage is obtained by projecting
`x^{k,i} - t_k g^{k,i}` back onto `C`. -/
theorem incremental_projected_subgradient_method_inner_succ (k : ℕ) {i : ℕ} (hi : i < m) :
    x[k, i + 1] =
      metricProjection C hC_nonempty hC_closed hC_convex
        ((x[k, i] : E) - t k • g k x[k, i] ⟨i, hi⟩) := by
  -- Apply the generic successor-stage recursion to the current outer iterate `x[k]`.
  simpa using
    (incremental_projected_subgradient_inner_iterate_succ
      C hC_nonempty hC_closed hC_convex t g k x[k] (i := i) hi)

-- Proof sketch: unfold `incremental_projected_subgradient_method` at `k + 1`; the recursive
-- clause defines the next outer iterate as the inner stage obtained after `m` projected updates.
/-- One outer step of Algorithm 8.13 sets `x^{k+1}` equal to the final inner stage `x^{k,m}`. -/
theorem incremental_projected_subgradient_method_succ (k : ℕ) :
    x[k + 1] = x[k, m] := by
  -- The recursive clause defines the next outer iterate as the final inner stage `x[k,m]`.
  rfl

-- Proof sketch: unfold `incremental_projected_subgradient_method_is_admissible` and read off the
-- positivity clause.
/-- Under the admissibility condition, the stepsize chosen at iteration `k` is strictly positive.
-/
theorem incremental_projected_subgradient_method_stepsize_pos
    {f : Fin m → E → ℝ}
    (h :
      incremental_projected_subgradient_method_is_admissible
        f C hC_nonempty hC_closed hC_convex t g x0)
    (k : ℕ) :
    0 < t k := by
  -- The admissibility predicate stores strict stepsize positivity in its first conjunct.
  exact h.1 k

-- Proof sketch: unfold `incremental_projected_subgradient_method_is_admissible` and specialize
-- the componentwise subgradient clause at the given outer iteration `k` and component `i`.
/-- Under the admissibility condition, the chosen component direction at inner stage `i` of outer
iteration `k` is a Euclidean subgradient of the `i`-th summand at the current inner iterate. -/
theorem incremental_projected_subgradient_method_component_mem
    {f : Fin m → E → ℝ}
    (h :
      incremental_projected_subgradient_method_is_admissible
        f C hC_nonempty hC_closed hC_convex t g x0)
    (k : ℕ) (i : Fin m) :
    g k x[k, (i : ℕ)] i ∈
      euclideanSubdifferentialAt (f i) (x[k, (i : ℕ)] : E) := by
  -- The admissibility predicate stores the componentwise subgradient clause in its second field.
  exact h.2 k i

end

end
