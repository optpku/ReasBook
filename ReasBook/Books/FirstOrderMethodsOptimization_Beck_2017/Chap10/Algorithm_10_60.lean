/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_59

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable (h : E → ℝ) (C : Set E) (ell_h eps : PosReal) (x0 : C) (k : Nat)
variable [IsConvexLipschitzConstrainedMinimizationProblem h C (PosReal.toNNReal ell_h)]

/-- The internal paired recursion storing both the constrained S-FISTA state
`(x^(k-1), x^k, t_k)` and the textbook extrapolated point `y^k`. -/
private def constrainedSFistaTextbookStateAndY
    (eps : PosReal) (x0 : C) : ℕ → FISTAState E × E
  | 0 =>
      ({ xPrev := x0
         xCur := x0
         tCur := 1 }, x0)
  | k + 1 =>
      let (state, yk) := constrainedSFistaTextbookStateAndY eps x0 k
      let tNext := fista_momentum_update state.tCur
      let xNext := constrained_s_fista_next_iterate h C ell_h eps yk
      let nextState : FISTAState E :=
        { xPrev := state.xCur
          xCur := xNext
          tCur := tNext }
      let yNext := xNext + ((state.tCur - 1) / tNext) • (xNext - state.xCur)
      (nextState, yNext)

/-- Algorithm 10.60. For a constrained convex Lipschitz problem `min { h(x) | x ∈ C }`,
an accuracy parameter `ε > 0`, and an initial feasible point `x^0 ∈ C`, the source-facing
projected S-FISTA recursion is the state sequence whose internal companion recursion stores both
the state `(x^(k-1), x^k, t_k)` and the textbook extrapolated point `y^k`. It starts from
`y^0 = x^0`, `t_0 = 1`, uses the source parameters `μ = ε / ell_h^2` and
`L̃ = ell_h^2 / ε`, and evolves by
`x^(k+1) = P_C (prox_(μ h) (y^k))`,
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`, and
`y^(k+1) = x^(k+1) + ((t_k - 1) / t_(k+1)) • (x^(k+1) - x^k)`. -/
def constrained_s_fista_textbook
    (eps : PosReal) (x0 : C) : ℕ → FISTAState E :=
  fun k ↦ (constrainedSFistaTextbookStateAndY h C ell_h eps x0 k).1

/-- Every constrained S-FISTA textbook current iterate belongs to the feasible set `C`. -/
theorem constrained_s_fista_textbook_mem_constraint
    (eps : PosReal) (x0 : C) (k : ℕ) :
    (constrained_s_fista_textbook h C ell_h eps x0 k).xCur ∈ C := by
  -- The paired recursion stores the next feasible point directly in the `xCur` field.
  induction k with
  | zero =>
      simp [constrained_s_fista_textbook, constrainedSFistaTextbookStateAndY]
  | succ k hk =>
      simp [constrained_s_fista_textbook, constrainedSFistaTextbookStateAndY]

/-- The feasible iterate sequence `x^k` produced by the source-facing projected S-FISTA
recursion. -/
def constrained_s_fista_textbook_x
    (eps : PosReal) (x0 : C) : ℕ → C :=
  fun k ↦
    ⟨(constrained_s_fista_textbook h C ell_h eps x0 k).xCur,
      constrained_s_fista_textbook_mem_constraint h C ell_h eps x0 k⟩

/-- The ambient-space iterate sequence `x^k`, obtained by coercing the feasible iterates into
`E` for affine formulas. -/
def constrained_s_fista_textbook_x_point
    (eps : PosReal) (x0 : C) : ℕ → E :=
  fun k ↦ constrained_s_fista_textbook_x h C ell_h eps x0 k

/-- The source-facing projected S-FISTA extrapolated sequence `y^k`. -/
def constrained_s_fista_textbook_y
    (eps : PosReal) (x0 : C) : ℕ → E :=
  fun k ↦ (constrainedSFistaTextbookStateAndY h C ell_h eps x0 k).2

/-- The momentum field carried by the source-facing projected S-FISTA state is the canonical
Chapter 10 FISTA momentum sequence. -/
theorem constrained_s_fista_textbook_tCur_eq
    (eps : PosReal) (x0 : C) (k : Nat) :
    (constrained_s_fista_textbook h C ell_h eps x0 k).tCur =
      fista_momentum_sequence k := by
  -- The state projection follows the same scalar momentum recursion as Algorithm 10.59.
  induction k with
  | zero =>
      simp [constrained_s_fista_textbook, constrainedSFistaTextbookStateAndY,
        fista_momentum_sequence]
  | succ k hk =>
      -- Freeze the predecessor pair so the successor state's momentum field becomes explicit.
      cases hpair : constrainedSFistaTextbookStateAndY h C ell_h eps x0 k with
      | mk state yk =>
          have hkState : state.tCur = fista_momentum_sequence k := by
            simpa [constrained_s_fista_textbook, hpair] using hk
          simp [constrained_s_fista_textbook, constrainedSFistaTextbookStateAndY,
            fista_momentum_sequence_succ, hpair, hkState]

/-- The source-facing projected S-FISTA feasible sequence starts at the prescribed initial point
`x^0`. -/
@[simp] theorem constrained_s_fista_textbook_x_zero
    (eps : PosReal) (x0 : C) :
    constrained_s_fista_textbook_x h C ell_h eps x0 0 = x0 := by
  -- Unfolding the initial paired state shows that the feasible iterate is definitionally `x0`.
  apply Subtype.ext
  simp [constrained_s_fista_textbook_x, constrained_s_fista_textbook,
    constrainedSFistaTextbookStateAndY]

/-- The source-facing projected S-FISTA extrapolated sequence starts from `y^0 = x^0`. -/
@[simp] theorem constrained_s_fista_textbook_y_zero
    (eps : PosReal) (x0 : C) :
    constrained_s_fista_textbook_y h C ell_h eps x0 0 =
      constrained_s_fista_textbook_x_point h C ell_h eps x0 0 := by
  -- At time `0`, the paired recursion stores `y^0` as the same point as the initial iterate.
  simp [constrained_s_fista_textbook_y, constrained_s_fista_textbook_x_point,
    constrained_s_fista_textbook_x, constrained_s_fista_textbook,
    constrainedSFistaTextbookStateAndY]

/-- Each source-facing projected S-FISTA successor iterate satisfies
`x^(k+1) = P_C (prox_(μ h) (y^k))`. -/
theorem constrained_s_fista_textbook_x_succ
    (eps : PosReal) (x0 : C) (k : Nat) :
    constrained_s_fista_textbook_x h C ell_h eps x0 (k + 1) =
      constrained_s_fista_next_iterate h C ell_h eps
        (constrained_s_fista_textbook_y h C ell_h eps x0 k) := by
  -- The successor state's `xCur` field is exactly the projected-proximal update of `y^k`.
  apply Subtype.ext
  simp [constrained_s_fista_textbook_x, constrained_s_fista_textbook,
    constrained_s_fista_textbook_y, constrainedSFistaTextbookStateAndY]

/-- The source-facing projected S-FISTA extrapolated sequence satisfies
`y^(k+1) = x^(k+1) + ((t_k - 1) / t_(k+1)) • (x^(k+1) - x^k)`. -/
theorem constrained_s_fista_textbook_y_succ
    (eps : PosReal) (x0 : C) (k : Nat) :
    constrained_s_fista_textbook_y h C ell_h eps x0 (k + 1) =
      constrained_s_fista_textbook_x_point h C ell_h eps x0 (k + 1) +
        ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
          (constrained_s_fista_textbook_x_point h C ell_h eps x0 (k + 1) -
            constrained_s_fista_textbook_x_point h C ell_h eps x0 k) := by
  -- Freeze the predecessor pair so the stored affine update is written in terms of a concrete
  -- predecessor state and extrapolated point.
  cases hpair : constrainedSFistaTextbookStateAndY h C ell_h eps x0 k with
  | mk state yk =>
      -- Identify the predecessor momentum with the canonical FISTA sequence.
      have ht : state.tCur = fista_momentum_sequence k := by
        simpa [constrained_s_fista_textbook, hpair] using
          (constrained_s_fista_textbook_tCur_eq h C ell_h eps x0 k)
      have htNext :
          fista_momentum_update state.tCur = fista_momentum_sequence (k + 1) := by
        rw [ht, ← fista_momentum_sequence_succ k]
      -- With the predecessor pair fixed, both sides reduce to the same affine formula.
      simp [constrained_s_fista_textbook_y, constrainedSFistaTextbookStateAndY,
        constrained_s_fista_textbook_x_point, constrained_s_fista_textbook_x,
        constrained_s_fista_textbook, hpair, ht]
      rw [← fista_momentum_update_eq (fista_momentum_sequence k),
        ← fista_momentum_sequence_succ k]

/- The underlying constrained S-FISTA textbook state owner. -/
#check constrained_s_fista_textbook h C ell_h eps x0

/- The feasible iterate sequence `x^k`. -/
#check constrained_s_fista_textbook_x h C ell_h eps x0

/- The ambient-space feasible iterate sequence `x^k`. -/
#check constrained_s_fista_textbook_x_point h C ell_h eps x0

/- The source-facing extrapolated sequence `y^k`. -/
#check constrained_s_fista_textbook_y h C ell_h eps x0

/- The source smoothing parameter `μ = ε / ell_h^2`. -/
#check constrained_s_fista_smoothing_parameter eps ell_h

/- The source curvature parameter `L̃ = ell_h^2 / ε`. -/
#check constrained_s_fista_curvature_parameter eps ell_h

/- The initialization `x^0 = x0`. -/
#check constrained_s_fista_textbook_x_zero h C ell_h eps x0

/- The initialization `y^0 = x^0`. -/
#check constrained_s_fista_textbook_y_zero h C ell_h eps x0

/- The projected proximal update `x^(k+1) = P_C (prox_(μ h) (y^k))`. -/
#check constrained_s_fista_textbook_x_succ h C ell_h eps x0 k

/- The canonical FISTA momentum identification for the state field `t_k`. -/
#check constrained_s_fista_textbook_tCur_eq h C ell_h eps x0 k

/- The extrapolation formula for `y^(k+1)`. -/
#check constrained_s_fista_textbook_y_succ h C ell_h eps x0 k

end
