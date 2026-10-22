/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_1

-- Declarations for this item will be appended below by the statement pipeline.

universe w

noncomputable section

section

variable {E1 E2 : Type w}

-- `lean_leansearch` is unavailable in this agent environment; this repair follows the local
-- Chapter 14 API already present in the workspace.
/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby Chapter 14 alternating-minimization files.

Algorithm 14.8 is `source-facing`: it gives a two-block Gauss-Seidel minimization scheme with a
derived half-step state `x^{k+1/2} = (x_1^{k+1}, x_2^k)`. Domain sampling against the Chapter 14
API shows the following owner split.
- `core/canonical`: `alternating_minimization_block_objective` and
  `is_alternating_minimization_trajectory` from Algorithm 14.1;
- `source-facing`: the product-space objective `f(x₁, x₂) + g₁(x₁) + g₂(x₂)`, the two slice
  objectives, and the half-step state `(x₁^{k+1}, x₂^k)`;
- `bridge/view`: the identification of a pair `(x₁, x₂)` with a dependent `Fin 2` block vector.

Accordingly, this file keeps the pair-valued source-facing helpers and the textbook two-block
trajectory clauses as primitive public data. As in the nearby Algorithm 14.2 API, effective-domain
membership is not primitive trajectory data here; it is a separate bridge hypothesis used only to
recover the canonical Algorithm 14.1 `Fin 2` trajectory. The only additional bridge data needed
is therefore the canonical `Fin 2` dependent-family view of a pair. -/

/-- The dependent `Fin 2` block family underlying the two-block product space `E₁ × E₂`. -/
abbrev two_block_alternating_minimization_space
    (E1 E2 : Type w) : Fin 2 → Type w :=
  Fin.cases E1 (fun _ ↦ E2)

/-- The canonical `Fin 2` block-vector view of a pair `(x₁, x₂)`. -/
abbrev two_block_alternating_minimization_state
    (x1 : E1) (x2 : E2) :
    (i : Fin 2) → two_block_alternating_minimization_space E1 E2 i :=
  Fin.cases x1 (fun _ ↦ x2)

/-- The coordinate view of pair iterates as a `Fin 2` alternating-minimization trajectory. -/
def two_block_alternating_minimization_block_iterate
    (x1 : ℕ → E1) (x2 : ℕ → E2) :
    ℕ → (i : Fin 2) → two_block_alternating_minimization_space E1 E2 i :=
  fun k ↦ two_block_alternating_minimization_state (x1 k) (x2 k)

@[simp] theorem two_block_alternating_minimization_state_zero
    (x1 : E1) (x2 : E2) :
    two_block_alternating_minimization_state x1 x2 0 = x1 :=
  rfl

@[simp] theorem two_block_alternating_minimization_state_one
    (x1 : E1) (x2 : E2) :
    two_block_alternating_minimization_state x1 x2 1 = x2 :=
  rfl

@[simp] theorem two_block_alternating_minimization_block_iterate_zero
    (x1 : ℕ → E1) (x2 : ℕ → E2) (k : ℕ) :
    two_block_alternating_minimization_block_iterate x1 x2 k 0 = x1 k :=
  rfl

@[simp] theorem two_block_alternating_minimization_block_iterate_one
    (x1 : ℕ → E1) (x2 : ℕ → E2) (k : ℕ) :
    two_block_alternating_minimization_block_iterate x1 x2 k 1 = x2 k :=
  rfl

/-- The full two-block objective `F(x₁, x₂) = f(x₁, x₂) + g₁(x₁) + g₂(x₂)` on the product
space `E₁ × E₂`. -/
def two_block_alternating_minimization_objective
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal) : E1 × E2 → EReal
  | (x1, x2) => f (x1, x2) + g1 x1 + g2 x2

@[simp] theorem two_block_alternating_minimization_objective_apply
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal)
    (x1 : E1) (x2 : E2) :
    two_block_alternating_minimization_objective f g1 g2 (x1, x2) =
      f (x1, x2) + g1 x1 + g2 x2 :=
  rfl

/-- The canonical `Fin 2` block-vector view of the full two-block objective, used to specialize
Algorithm 14.1 to the pair-valued setting of Algorithm 14.8. -/
def two_block_alternating_minimization_objective_blocks
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal) :
    ((i : Fin 2) → two_block_alternating_minimization_space E1 E2 i) → EReal :=
  fun x ↦ two_block_alternating_minimization_objective f g1 g2 (x 0, x 1)

@[simp] theorem two_block_alternating_minimization_objective_blocks_apply
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal)
    (x : (i : Fin 2) → two_block_alternating_minimization_space E1 E2 i) :
    two_block_alternating_minimization_objective_blocks f g1 g2 x =
      f (x 0, x 1) + g1 (x 0) + g2 (x 1) :=
  rfl

/-- The `x₁`-subproblem in two-block alternating minimization with the second block frozen at
`x2`, namely the full one-variable section `x1 ↦ f(x1, x2) + g1(x1) + g2(x2)`. -/
def two_block_alternating_minimization_x1_objective
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal) (x2 : E2) : E1 → EReal :=
  fun x1 ↦ two_block_alternating_minimization_objective f g1 g2 (x1, x2)

-- Proof sketch: unfold `two_block_alternating_minimization_x1_objective`; evaluation at `x1` is
-- definitionally the displayed one-block objective with `x2` fixed.
/-- Evaluating the `x₁`-subproblem objective gives the expression
`f(x₁, x₂) + g₁(x₁) + g₂(x₂)`. -/
@[simp] theorem two_block_alternating_minimization_x1_objective_apply
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal) (x2 : E2) (x1 : E1) :
    two_block_alternating_minimization_x1_objective f g1 g2 x2 x1 =
      f (x1, x2) + g1 x1 + g2 x2 :=
  rfl

/-- The `x₂`-subproblem in two-block alternating minimization with the first block frozen at
`x1`, namely the full one-variable section `x2 ↦ f(x1, x2) + g1(x1) + g2(x2)`. -/
def two_block_alternating_minimization_x2_objective
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal) (x1 : E1) : E2 → EReal :=
  fun x2 ↦ two_block_alternating_minimization_objective f g1 g2 (x1, x2)

-- Proof sketch: unfold `two_block_alternating_minimization_x2_objective`; evaluation at `x2` is
-- definitionally the displayed one-block objective with `x1` fixed.
/-- Evaluating the `x₂`-subproblem objective gives the expression
`f(x₁, x₂) + g₁(x₁) + g₂(x₂)`. -/
@[simp] theorem two_block_alternating_minimization_x2_objective_apply
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal) (x1 : E1) (x2 : E2) :
    two_block_alternating_minimization_x2_objective f g1 g2 x1 x2 =
      f (x1, x2) + g1 x1 + g2 x2 :=
  rfl

/-- Helper for Algorithm 14.8: the block-`0` mixed state in the canonical `Fin 2` owner is just
the pair state with the candidate first block and the old second block. -/
@[simp] theorem two_block_partial_state_zero_eq_state
    (x1k x1Next : E1) (x2k x2Next : E2) (x1 : E1) :
    alternating_minimization_partial_state
        (two_block_alternating_minimization_state x1k x2k)
        (two_block_alternating_minimization_state x1Next x2Next)
        0
        x1 =
      two_block_alternating_minimization_state x1 x2k := by
  -- Normalize the `Fin 2` mixed state coordinatewise; there is no block before `0`.
  funext j
  fin_cases j
  · simp [alternating_minimization_partial_state]
  · simp [alternating_minimization_partial_state]

/-- Helper for Algorithm 14.8: the block-`1` mixed state in the canonical `Fin 2` owner is just
the pair state with the new first block and the candidate second block. -/
@[simp] theorem two_block_partial_state_one_eq_state
    (x1k x1Next : E1) (x2k x2Next : E2) (x2 : E2) :
    alternating_minimization_partial_state
        (two_block_alternating_minimization_state x1k x2k)
        (two_block_alternating_minimization_state x1Next x2Next)
        1
        x2 =
      two_block_alternating_minimization_state x1Next x2 := by
  -- Normalize the `Fin 2` mixed state coordinatewise; block `0` comes from `xNext`.
  funext j
  fin_cases j
  · simp [alternating_minimization_partial_state]
  · simp [alternating_minimization_partial_state]

@[simp] theorem two_block_alternating_minimization_block_objective_zero_apply
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal)
    (x1k x1Next : E1) (x2k x2Next : E2) (x1 : E1) :
    alternating_minimization_block_objective
        (two_block_alternating_minimization_objective_blocks f g1 g2)
        (two_block_alternating_minimization_state x1k x2k)
        (two_block_alternating_minimization_state x1Next x2Next)
        0
        x1 =
      two_block_alternating_minimization_x1_objective f g1 g2 x2k x1 := by
  -- Rewrite the canonical block-`0` objective through the normalized mixed state.
  simp [alternating_minimization_block_objective_apply]

@[simp] theorem two_block_alternating_minimization_block_objective_one_apply
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal)
    (x1k x1Next : E1) (x2k x2Next : E2) (x2 : E2) :
    alternating_minimization_block_objective
        (two_block_alternating_minimization_objective_blocks f g1 g2)
        (two_block_alternating_minimization_state x1k x2k)
        (two_block_alternating_minimization_state x1Next x2Next)
        1
        x2 =
      two_block_alternating_minimization_x2_objective f g1 g2 x1Next x2 := by
  -- Rewrite the canonical block-`1` objective through the normalized mixed state.
  simp [alternating_minimization_block_objective_apply]

/-- The auxiliary half-step state `x^{k+1/2}` of Algorithm 14.8, obtained after the `x₁`-update
and before the `x₂`-update. -/
def two_block_alternating_minimization_half_step
    (x1 : ℕ → E1) (x2 : ℕ → E2) (k : ℕ) : E1 × E2 :=
  (x1 (k + 1), x2 k)

-- Proof sketch: unfold `two_block_alternating_minimization_half_step`; the first component of the
-- defining pair is `x1 (k + 1)`.
/-- The first component of the half-step state is the newly updated first block `x₁^{k+1}`. -/
@[simp] theorem two_block_alternating_minimization_half_step_fst
    (x1 : ℕ → E1) (x2 : ℕ → E2) (k : ℕ) :
    (two_block_alternating_minimization_half_step x1 x2 k).1 = x1 (k + 1) :=
  rfl

-- Proof sketch: unfold `two_block_alternating_minimization_half_step`; the second component of
-- the defining pair is `x2 k`.
/-- The second component of the half-step state is the old second block `x₂^k`. -/
@[simp] theorem two_block_alternating_minimization_half_step_snd
    (x1 : ℕ → E1) (x2 : ℕ → E2) (k : ℕ) :
    (two_block_alternating_minimization_half_step x1 x2 k).2 = x2 k :=
  rfl

/-- At each iteration `k`, the canonical Chapter 14 alternating-minimization trajectory on the
`Fin 2` block-vector view gives exactly the two textbook blockwise minimization clauses of
Algorithm 14.8. -/
theorem two_block_alternating_minimization_step
    {f : E1 × E2 → EReal} {g1 : E1 → EReal} {g2 : E2 → EReal}
    {x1 : ℕ → E1} {x2 : ℕ → E2}
    (h :
      is_alternating_minimization_trajectory
        (two_block_alternating_minimization_objective_blocks f g1 g2)
        (two_block_alternating_minimization_block_iterate x1 x2))
    (k : ℕ) :
    IsMinOn
        (two_block_alternating_minimization_x1_objective f g1 g2 (x2 k))
        Set.univ
        (x1 (k + 1)) ∧
    IsMinOn
        (two_block_alternating_minimization_x2_objective f g1 g2 (x1 (k + 1)))
        Set.univ
        (x2 (k + 1)) := by
  -- Read the two canonical `Fin 2` blockwise minimizing clauses at indices `0` and `1`.
  constructor
  · simpa using is_alternating_minimization_trajectory_step h k 0
  · simpa using is_alternating_minimization_trajectory_step h k 1

/-- The textbook two-block step clauses imply the canonical Chapter 14 alternating-minimization
trajectory for the `Fin 2` block-vector view of the iterates, once the initial point lies in the
effective domain of the full two-block objective. -/
theorem is_alternating_minimization_trajectory_of_two_block_steps
    {f : E1 × E2 → EReal} {g1 : E1 → EReal} {g2 : E2 → EReal}
    {x1 : ℕ → E1} {x2 : ℕ → E2}
    (hx0 :
      two_block_alternating_minimization_block_iterate x1 x2 0 ∈
        effective_domain (two_block_alternating_minimization_objective_blocks f g1 g2))
    (hstep :
      ∀ k : ℕ,
        IsMinOn
          (two_block_alternating_minimization_x1_objective f g1 g2 (x2 k))
          Set.univ
          (x1 (k + 1)) ∧
        IsMinOn
          (two_block_alternating_minimization_x2_objective f g1 g2 (x1 (k + 1)))
          Set.univ
          (x2 (k + 1))) :
    is_alternating_minimization_trajectory
      (two_block_alternating_minimization_objective_blocks f g1 g2)
      (two_block_alternating_minimization_block_iterate x1 x2) := by
  refine ⟨hx0, ?_⟩
  intro k i
  rcases hstep k with ⟨hx1, hx2⟩
  -- Split on the two blocks of `Fin 2`; each branch is exactly one source-facing step clause.
  fin_cases i
  · simpa using hx1
  · simpa using hx2

/-- Algorithm 14.8 in source-facing pair form: `x₂⁰` minimizes the initial second-block slice,
and for every iteration `k` the updates `x₁^(k+1)` and `x₂^(k+1)` minimize their respective frozen
one-variable subproblems. Effective-domain membership of `(x₁⁰, x₂⁰)` is a separate bridge
hypothesis when passing to the canonical Chapter 14 trajectory owner. -/
@[mk_iff is_two_block_alternating_minimization_trajectory_iff]
class is_two_block_alternating_minimization_trajectory
    (f : E1 × E2 → EReal) (g1 : E1 → EReal) (g2 : E2 → EReal)
    (x1 : ℕ → E1) (x2 : ℕ → E2) : Prop where
  initial :
    IsMinOn
      (two_block_alternating_minimization_x2_objective f g1 g2 (x1 0))
      Set.univ
      (x2 0)
  step_x1 (k : ℕ) :
    IsMinOn
      (two_block_alternating_minimization_x1_objective f g1 g2 (x2 k))
      Set.univ
      (x1 (k + 1))
  step_x2 (k : ℕ) :
    IsMinOn
      (two_block_alternating_minimization_x2_objective f g1 g2 (x1 (k + 1)))
      Set.univ
      (x2 (k + 1))

/-- A source-facing two-block trajectory canonically yields the initial second-block minimization
clause as a typeclass-searchable fact. -/
instance two_block_alternating_minimization_trajectory_initial_fact
    {f : E1 × E2 → EReal} {g1 : E1 → EReal} {g2 : E2 → EReal}
    {x1 : ℕ → E1} {x2 : ℕ → E2}
    [h : is_two_block_alternating_minimization_trajectory f g1 g2 x1 x2] :
    Fact
      (IsMinOn
        (two_block_alternating_minimization_x2_objective f g1 g2 (x1 0))
        Set.univ
        (x2 0)) where
  out := h.initial

/-- A source-facing two-block trajectory canonically yields the underlying Chapter 14 trajectory. -/
theorem is_two_block_alternating_minimization_trajectory_toTrajectory
    {f : E1 × E2 → EReal} {g1 : E1 → EReal} {g2 : E2 → EReal}
    {x1 : ℕ → E1} {x2 : ℕ → E2}
    (hx0 :
      two_block_alternating_minimization_block_iterate x1 x2 0 ∈
        effective_domain (two_block_alternating_minimization_objective_blocks f g1 g2))
    (h : is_two_block_alternating_minimization_trajectory f g1 g2 x1 x2) :
    is_alternating_minimization_trajectory
      (two_block_alternating_minimization_objective_blocks f g1 g2)
      (two_block_alternating_minimization_block_iterate x1 x2) :=
  is_alternating_minimization_trajectory_of_two_block_steps
    hx0
    (fun k ↦ ⟨h.step_x1 k, h.step_x2 k⟩)

/-- Each source-facing outer iteration satisfies the two blockwise minimization clauses. -/
theorem is_two_block_alternating_minimization_trajectory_step
    {f : E1 × E2 → EReal} {g1 : E1 → EReal} {g2 : E2 → EReal}
    {x1 : ℕ → E1} {x2 : ℕ → E2}
    (h : is_two_block_alternating_minimization_trajectory f g1 g2 x1 x2)
    (k : ℕ) :
    IsMinOn
        (two_block_alternating_minimization_x1_objective f g1 g2 (x2 k))
        Set.univ
        (x1 (k + 1)) ∧
      IsMinOn
        (two_block_alternating_minimization_x2_objective f g1 g2 (x1 (k + 1)))
        Set.univ
        (x2 (k + 1)) :=
  ⟨h.step_x1 k, h.step_x2 k⟩

/-- Bridge/view: specializing the canonical Chapter 14 trajectory owner to `Fin 2` rewrites its
clauses as the effective-domain condition and the recursive two-block `x₁`- and
`x₂`-minimization rules. The separate textbook initialization clause for `x₂⁰` is recorded by
`is_two_block_alternating_minimization_trajectory`. -/
theorem is_alternating_minimization_trajectory_two_block_iff
    {f : E1 × E2 → EReal} {g1 : E1 → EReal} {g2 : E2 → EReal}
    {x1 : ℕ → E1} {x2 : ℕ → E2} :
    is_alternating_minimization_trajectory
        (two_block_alternating_minimization_objective_blocks f g1 g2)
        (two_block_alternating_minimization_block_iterate x1 x2) ↔
      two_block_alternating_minimization_block_iterate x1 x2 0 ∈
          effective_domain (two_block_alternating_minimization_objective_blocks f g1 g2) ∧
        ∀ k : ℕ,
          IsMinOn
            (two_block_alternating_minimization_x1_objective f g1 g2 (x2 k))
            Set.univ
            (x1 (k + 1)) ∧
          IsMinOn
            (two_block_alternating_minimization_x2_objective f g1 g2 (x1 (k + 1)))
            Set.univ
            (x2 (k + 1)) := by
  constructor
  · intro h
    exact ⟨is_alternating_minimization_trajectory_zero h,
      two_block_alternating_minimization_step h⟩
  · rintro ⟨hx0, hstep⟩
    exact is_alternating_minimization_trajectory_of_two_block_steps hx0 hstep

end
