/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_1
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Definition_14_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open scoped Gradient

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)]

local notation "BlockSpace" => PiLp (2 : ENNReal) Ei

/- `prompt_add/` is absent in this workspace, so the statement design is sampled from the nearby
block-optimization owners in Chapter 11 and the set-valued trajectory pattern used throughout
Chapters 10, 12, and 13.

Algorithm 14.2 is `source-facing`: the source explicitly names the inner states `x^{k,i}` and
chooses, at each block, an arbitrary minimizer of the one-block problem
`y ↦ F(x^{k,i-1} + U_i (y - x_i^k))`.

Domain sampling identifies the following owner split.
- `core/canonical`: `alternating_minimization_block_objective` from Algorithm 14.1 for the
  Gauss-Seidel one-block objective, and `alternating_minimization_auxiliary_iterate` from
  Definition 14.1 for the canonical mixed inner state determined by an outer trajectory;
- `source-facing`: the explicit affine block replacement
  `z + 𝒰[i] (y - x_i^k)` and the alternative-form trajectory with named inner states;
- `bridge/view`: the set-valued one-block step together with theorems connecting the explicit
  inner-state surface to the canonical owners above.

Accordingly, this file deletes the duplicate local minimizer-set wrapper, keeps only the
source-facing alternative-step surface, and bridges it back to the canonical Chapter 14 owners
instead of maintaining a parallel API. -/

/-- The admissible next inner states after updating block `i` from the current auxiliary point `z`
with outer iterate `xk`: choose a minimizer `ỹ` of the one-block objective and set the next point
to `z + 𝒰[i] (ỹ - x_i^k)`. -/
def alternating_minimization_block_step
    (F : BlockSpace → EReal) (xk z : BlockSpace) (i : Fin p) : Set BlockSpace :=
  {xNext | ∃ y : Ei i, IsMinOn (fun y ↦ F (z + 𝒰[i] (y - xk i))) Set.univ y ∧
      xNext = z + 𝒰[i] (y - xk i)}

-- Proof sketch: unfold `alternating_minimization_block_step`; membership in the image is
-- equivalent to the existence of a minimizing block value `y` whose affine block replacement is
-- the proposed next inner state.
/-- A point belongs to the one-block update set exactly when it is obtained from the current
auxiliary state `z` by replacing the `i`-th block with some minimizer of
`y ↦ F(z + 𝒰[i] (y - x_i^k))`. -/
@[simp] theorem mem_alternating_minimization_block_step_iff
    {F : BlockSpace → EReal} {xk z xNext : BlockSpace} {i : Fin p} :
    xNext ∈ alternating_minimization_block_step F xk z i ↔
      ∃ y : Ei i,
        IsMinOn (fun y ↦ F (z + 𝒰[i] (y - xk i))) Set.univ y ∧
          xNext = z + 𝒰[i] (y - xk i) := by
  rfl

/-- Algorithm 14.2: sequences of outer iterates `x^k` and auxiliary states `x^{k,i}` follow the
alternating minimization method in alternative form from initialization `x⁰ = x0` when, for every
outer iteration `k`, one has `x^{k,0} = x^k`, each inner successor state `x^{k,i}` is obtained
from `x^{k,i-1}` by updating block `i` with a minimizer of
`y ↦ F(x^{k,i-1} + 𝒰[i] (y - x_i^k))`, and the next outer iterate is the terminal inner state
`x^(k+1) = x^{k,p}`. -/
class is_alternating_minimization_alternative_trajectory
    (F : BlockSpace → EReal) (x0 : BlockSpace) (x : ℕ → BlockSpace)
    (xAux : ℕ → Fin (p + 1) → BlockSpace) : Prop where
  zero_eq : x 0 = x0
  start_eq : ∀ k : ℕ, xAux k 0 = x k
  block_mem : ∀ k : ℕ, ∀ i : Fin p,
    xAux k i.succ ∈
      alternating_minimization_block_step F (x k) (xAux k i.castSucc) i
  terminal_eq : ∀ k : ℕ, x (k + 1) = xAux k (Fin.last p)

/-- The source-facing alternative trajectory owner exposes its defining clauses to typeclass
search. -/
instance instFactAlternatingMinimizationAlternativeTrajectoryClauses
    {F : BlockSpace → EReal} {x0 : BlockSpace} {x : ℕ → BlockSpace}
    {xAux : ℕ → Fin (p + 1) → BlockSpace}
    [h : is_alternating_minimization_alternative_trajectory F x0 x xAux] :
    Fact
      (x 0 = x0 ∧
        ∀ k : ℕ,
          xAux k 0 = x k ∧
            (∀ i : Fin p,
              xAux k i.succ ∈
                alternating_minimization_block_step F (x k) (xAux k i.castSucc) i) ∧
            x (k + 1) = xAux k (Fin.last p)) where
  out := ⟨h.zero_eq, fun k ↦ ⟨h.start_eq k, h.block_mem k, h.terminal_eq k⟩⟩

-- Proof sketch: extract the initialization clause from the first conjunct of
-- `is_alternating_minimization_alternative_trajectory F x0 x xAux`.
/-- An alternating-minimization trajectory in alternative form starts from the prescribed outer
iterate `x⁰ = x0`. -/
theorem is_alternating_minimization_alternative_trajectory_zero
    {F : BlockSpace → EReal} {x0 : BlockSpace} {x : ℕ → BlockSpace}
    {xAux : ℕ → Fin (p + 1) → BlockSpace}
    (h : is_alternating_minimization_alternative_trajectory F x0 x xAux) :
    x 0 = x0 :=
  h.zero_eq

-- Proof sketch: specialize the defining universal clause of
-- `is_alternating_minimization_alternative_trajectory F x0 x xAux` at the iteration index `k`.
/-- At each outer iteration `k`, the auxiliary cycle starts at `x^{k,0} = x^k`, every block
successor `x^{k,i}` belongs to the corresponding one-block update set, and the next outer iterate
is the terminal state `x^(k+1) = x^{k,p}`. -/
theorem is_alternating_minimization_alternative_trajectory_step
    {F : BlockSpace → EReal} {x0 : BlockSpace} {x : ℕ → BlockSpace}
    {xAux : ℕ → Fin (p + 1) → BlockSpace}
    (h : is_alternating_minimization_alternative_trajectory F x0 x xAux) (k : ℕ) :
    xAux k 0 = x k ∧
      (∀ i : Fin p,
        xAux k i.succ ∈
          alternating_minimization_block_step F (x k) (xAux k i.castSucc) i) ∧
      x (k + 1) = xAux k (Fin.last p) :=
  ⟨h.start_eq k, h.block_mem k, h.terminal_eq k⟩

/-- Helper for Algorithm 14.2: before block `i` is updated, the `i`-th coordinate of the
auxiliary state still matches the old outer iterate `x^k`. -/
theorem alternative_trajectory_coordinate_before_own_update
    {F : BlockSpace → EReal} {x0 : BlockSpace} {x : ℕ → BlockSpace}
    {xAux : ℕ → Fin (p + 1) → BlockSpace}
    (h : is_alternating_minimization_alternative_trajectory F x0 x xAux)
    (k : ℕ) (i : Fin p) :
    xAux k i.castSucc i = x k i := by
  let hstep := is_alternating_minimization_alternative_trajectory_step h k
  -- Follow the earlier block updates one by one; every block before `i` leaves coordinate `i`
  -- unchanged.
  have hprefix :
      ∀ n : ℕ, ∀ hn : n ≤ i.1,
        xAux k ⟨n, Nat.lt_succ_of_le (Nat.le_trans hn i.isLt.le)⟩ i = x k i := by
    intro n
    induction n with
    | zero =>
        intro hn
        -- At the start of the inner cycle, `xAux k 0 = x k`.
        simpa using congrArg (fun z : BlockSpace ↦ z i) hstep.1
    | succ n ihn =>
        intro hn
        let b : Fin p := ⟨n, lt_of_lt_of_le (Nat.lt_of_succ_le hn) i.isLt.le⟩
        rcases (mem_alternating_minimization_block_step_iff.mp (hstep.2.1 b)) with
          ⟨y, hyMin, hyEq⟩
        have hbne : b ≠ i := by
          exact Fin.ne_of_lt (show b < i from Nat.lt_of_succ_le hn)
        -- Updating block `b < i` does not affect coordinate `i`.
        calc
          xAux k ⟨n.succ, Nat.lt_succ_of_le (Nat.le_trans hn i.isLt.le)⟩ i
              = (xAux k b.castSucc + 𝒰[b] (y - x k b)) i := by
                  simpa [b] using congrArg (fun z : BlockSpace ↦ z i) hyEq
          _ = xAux k b.castSucc i := by
                simp [hbne]
          _ = x k i := by
                simpa [b] using ihn (Nat.le_of_succ_le hn)
  -- Specialize the prefix invariance at the exact step before block `i` is updated.
  simpa using hprefix i.1 (le_rfl : i.1 ≤ i.1)

/-- Helper for Algorithm 14.2: after block `i` is updated, later block updates preserve its
coordinate all the way to the terminal inner state `x^{k,p}`. -/
theorem alternative_trajectory_coordinate_preserved_to_last
    {F : BlockSpace → EReal} {x0 : BlockSpace} {x : ℕ → BlockSpace}
    {xAux : ℕ → Fin (p + 1) → BlockSpace}
    (h : is_alternating_minimization_alternative_trajectory F x0 x xAux)
    (k : ℕ) (i : Fin p) :
    xAux k (Fin.last p) i = xAux k i.succ i := by
  let hstep := is_alternating_minimization_alternative_trajectory_step h k
  -- After the `i`-th update, every later block update occurs at an index strictly larger than `i`
  -- and therefore leaves coordinate `i` fixed.
  have hsuffix :
      ∀ n : ℕ, ∀ hn : i.1 + 1 + n ≤ p,
        xAux k ⟨i.1 + 1 + n, Nat.lt_succ_of_le hn⟩ i = xAux k i.succ i := by
    intro n
    induction n with
    | zero =>
        intro hn
        rfl
    | succ n ihn =>
        intro hn
        let b : Fin p := ⟨i.1 + 1 + n, by
          have hb : i.1 + 1 + n < p := by omega
          exact hb⟩
        rcases (mem_alternating_minimization_block_step_iff.mp (hstep.2.1 b)) with
          ⟨y, hyMin, hyEq⟩
        have hbine : i ≠ b := by
          exact Fin.ne_of_lt (by
            change i.1 < i.1 + 1 + n
            omega)
        -- Updating a later block `b > i` leaves coordinate `i` unchanged.
        calc
          xAux k ⟨i.1 + 1 + n.succ, Nat.lt_succ_of_le hn⟩ i
              = (xAux k b.castSucc + 𝒰[b] (y - x k b)) i := by
                  simpa [Nat.add_assoc, b] using congrArg (fun z : BlockSpace ↦ z i) hyEq
          _ = xAux k b.castSucc i := by
                simp [hbine]
          _ = xAux k i.succ i := by
                have hn' : i.1 + 1 + n ≤ p := by omega
                simpa [Nat.add_assoc, b] using ihn hn'
  -- Evaluate the suffix invariance at the number of remaining block updates.
  have hi : i.1 + 1 ≤ p := Nat.succ_le_of_lt i.isLt
  have hlast :
      xAux k
          ⟨i.1 + 1 + (p - (i.1 + 1)),
            Nat.lt_succ_of_le (by
              simp [Nat.add_sub_of_le hi])⟩
          i =
        xAux k i.succ i :=
    hsuffix (p - (i.1 + 1)) (by
      simp [Nat.add_sub_of_le hi])
  simpa [Nat.add_assoc, Nat.add_sub_of_le hi] using hlast

/-- Helper for Algorithm 14.2: the block value chosen when updating block `i` is exactly the
`i`-th coordinate of the next outer iterate `x^(k+1)`. -/
theorem alternative_trajectory_updated_value_eq_next_coordinate
    {F : BlockSpace → EReal} {x0 : BlockSpace} {x : ℕ → BlockSpace}
    {xAux : ℕ → Fin (p + 1) → BlockSpace}
    (h : is_alternating_minimization_alternative_trajectory F x0 x xAux)
    (k : ℕ) (i : Fin p) {y : Ei i}
    (hyEq : xAux k i.succ = xAux k i.castSucc + 𝒰[i] (y - x k i)) :
    y = x (k + 1) i := by
  let hstep := is_alternating_minimization_alternative_trajectory_step h k
  have hbefore := alternative_trajectory_coordinate_before_own_update h k i
  have hfreeze := alternative_trajectory_coordinate_preserved_to_last h k i
  have hcurrent : xAux k i.succ i = y := by
    -- Apply the explicit block update at the active coordinate and cancel the old value.
    calc
      xAux k i.succ i = (xAux k i.castSucc + 𝒰[i] (y - x k i)) i := by
        simpa using congrArg (fun z : BlockSpace ↦ z i) hyEq
      _ = xAux k i.castSucc i + (𝒰[i] (y - x k i)) i := rfl
      _ = x k i + (y - x k i) := by rw [hbefore, block_coordinate_embedding_apply_same]
      _ = y := by abel
  have hlast : xAux k (Fin.last p) i = x (k + 1) i := by
    -- The terminal inner state is the next outer iterate.
    simpa using congrArg (fun z : BlockSpace ↦ z i) hstep.2.2.symm
  -- The chosen value at block `i` persists to the terminal state, hence equals `x^(k+1)_i`.
  calc
    y = xAux k i.succ i := hcurrent.symm
    _ = xAux k (Fin.last p) i := hfreeze.symm
    _ = x (k + 1) i := hlast

-- Proof sketch: argue by induction on `i`. The base case is the defining clause
-- `xAux k 0 = x k`. For the successor step, unpack membership in
-- `alternating_minimization_block_step`, compare the resulting update point with
-- `alternating_minimization_auxiliary_iterate_succ_eq_add_single`, and conclude by the
-- induction hypothesis.
/-- Along an alternative-form trajectory, the explicit auxiliary states coincide with the canonical
mixed states from Definition 14.1. -/
theorem is_alternating_minimization_alternative_trajectory_auxiliary_iterate
    {F : BlockSpace → EReal} {x0 : BlockSpace} {x : ℕ → BlockSpace}
    {xAux : ℕ → Fin (p + 1) → BlockSpace}
    (h : is_alternating_minimization_alternative_trajectory F x0 x xAux)
    (k : ℕ) (i : Fin (p + 1)) :
    xAux k i = alternating_minimization_auxiliary_iterate x k i := by
  let hstep := is_alternating_minimization_alternative_trajectory_step h k
  induction i using Fin.induction with
  | zero =>
      -- Both auxiliary-state owners start from the current outer iterate `x^k`.
      rw [alternating_minimization_auxiliary_iterate_zero]
      exact hstep.1
  | succ i ih =>
      rcases (mem_alternating_minimization_block_step_iff.mp (hstep.2.1 i)) with
        ⟨y, hyMin, hyEq⟩
      have hy :
          y = x (k + 1) i :=
        alternative_trajectory_updated_value_eq_next_coordinate h k i hyEq
      -- Route correction: identify the source-facing explicit update with the canonical
      -- Definition 14.1 successor formula at the same block.
      calc
        xAux k i.succ = xAux k i.castSucc + 𝒰[i] (y - x k i) := hyEq
        _ = alternating_minimization_auxiliary_iterate x k i.castSucc +
              𝒰[i] (x (k + 1) i - x k i) := by rw [ih, hy]
        _ = alternating_minimization_auxiliary_iterate x k i.succ := by
              rw [alternating_minimization_auxiliary_iterate_succ_eq_add_single]

/-- Helper for Algorithm 14.2: the explicit affine block update from the textbook agrees with the
canonical Chapter 14 mixed state `alternating_minimization_partial_state`. -/
lemma explicit_block_update_eq_partial_state
    {x : ℕ → BlockSpace} (k : ℕ) (i : Fin p) (y : Ei i) :
    alternating_minimization_auxiliary_iterate x k i.castSucc + 𝒰[i] (y - x k i) =
      WithLp.toLp 2
        (alternating_minimization_partial_state
          (fun j ↦ x k j)
          (fun j ↦ x (k + 1) j)
          i
          y) := by
  -- Compare the explicit affine update and the canonical mixed state coordinatewise.
  ext j
  by_cases hji : j = i
  · subst hji
    simp [alternating_minimization_partial_state]
  · by_cases hjlt : j < i
    · simp [alternating_minimization_auxiliary_iterate_apply,
        alternating_minimization_partial_state, hjlt, hji]
    · simp [alternating_minimization_auxiliary_iterate_apply,
        alternating_minimization_partial_state, hjlt, hji]

-- Proof sketch: specialize the step clause at `k` and the chosen block `i`, unpack the one-block
-- step membership, use
-- `is_alternating_minimization_alternative_trajectory_auxiliary_iterate` to identify the previous
-- inner state with the canonical mixed state `x^{k,i-1}`, then compare the chosen successor with
-- `alternating_minimization_auxiliary_iterate_succ_eq_add_single`. This identifies the
-- minimizing block value with `x (k + 1) i` and yields the canonical Algorithm 14.1 blockwise
-- `IsMinOn` clause.
/-- Every alternative-form trajectory satisfies the canonical Algorithm 14.1 blockwise minimization
condition for the coordinate view of the same outer iterates. -/
theorem is_alternating_minimization_alternative_trajectory_block_isMinOn
    {F : BlockSpace → EReal} {x0 : BlockSpace} {x : ℕ → BlockSpace}
    {xAux : ℕ → Fin (p + 1) → BlockSpace}
    (h : is_alternating_minimization_alternative_trajectory F x0 x xAux) (k : ℕ) (i : Fin p) :
    IsMinOn
      (alternating_minimization_block_objective
        (fun z : (j : Fin p) → Ei j ↦ F (WithLp.toLp 2 z))
        (fun j ↦ x k j)
        (fun j ↦ x (k + 1) j)
        i)
      Set.univ
      (x (k + 1) i) := by
  let hstep := is_alternating_minimization_alternative_trajectory_step h k
  rcases (mem_alternating_minimization_block_step_iff.mp (hstep.2.1 i)) with
    ⟨y, hyMin, hyEq⟩
  have haux :
      xAux k i.castSucc = alternating_minimization_auxiliary_iterate x k i.castSucc :=
    is_alternating_minimization_alternative_trajectory_auxiliary_iterate h k i.castSucc
  have hy :
      y = x (k + 1) i :=
    alternative_trajectory_updated_value_eq_next_coordinate h k i hyEq
  -- Transport the source-facing minimizing property through the canonical mixed-state adapter.
  rw [isMinOn_univ_iff]
  intro z
  have hyCompare := (isMinOn_iff.mp hyMin) z (by simp)
  simpa [alternating_minimization_block_objective_apply, haux, hy,
    explicit_block_update_eq_partial_state] using hyCompare

-- Proof sketch: combine the prescribed initial-domain hypothesis with the previous bridge theorem
-- `is_alternating_minimization_alternative_trajectory_block_isMinOn`.
/-- If the prescribed initialization `x0` lies in `dom(F)`, an alternative-form trajectory induces
the canonical Algorithm 14.1 trajectory on the coordinate view of the same outer iterates. -/
theorem is_alternating_minimization_alternative_trajectory_toTrajectory
    {F : BlockSpace → EReal} {x0 : BlockSpace} {x : ℕ → BlockSpace}
    {xAux : ℕ → Fin (p + 1) → BlockSpace}
    (hx0 : x0 ∈ effective_domain F)
    (h : is_alternating_minimization_alternative_trajectory F x0 x xAux) :
    is_alternating_minimization_trajectory
      (fun z : (i : Fin p) → Ei i ↦ F (WithLp.toLp 2 z))
      (fun k i ↦ x k i) := by
  refine ⟨?_, ?_⟩
  · -- Rewrite the coordinate view at time `0` back to the prescribed initialization `x0`.
    rw [mem_effective_domain] at hx0 ⊢
    simpa [is_alternating_minimization_alternative_trajectory_zero h] using hx0
  · -- The blockwise minimizing property is exactly the bridge proved above.
    intro k i
    exact is_alternating_minimization_alternative_trajectory_block_isMinOn h k i

end
