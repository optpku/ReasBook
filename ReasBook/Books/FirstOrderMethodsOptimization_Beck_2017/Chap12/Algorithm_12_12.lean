/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_12.Spaces
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open TwoDimensionalTV WithLp

variable {m n : ℕ}

/-- The auxiliary primal image `u = Aᵀ z + d` used in step (a) of the two-dimensional
anisotropic TV FDPG method, where `z` is the canonical `L²` dual pair in
`WithLp 2 (ℝ^(m × (n - 1)) × ℝ^((m - 1) × n))`. -/
def two_dimensional_tv_l1_fdpg_primal_point
    (d : MatrixSpace m n) (z : DualSpace m n) : MatrixSpace m n :=
  Aᵀ[m, n] z + d

/-- Evaluating the auxiliary primal image gives the owner-level step-(a) formula
`u = Aᵀ z + d`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_primal_point_apply
    (d : MatrixSpace m n) (z : DualSpace m n) (i : Fin m) (j : Fin n) :
    two_dimensional_tv_l1_fdpg_primal_point d z i j =
      Aᵀ[m, n] z i j + d i j := by
  -- Expand the primal-point owner and read off the matrix sum entrywise.
  rfl

/-- Evaluating the auxiliary primal image at the canonical dual pair `(p, q)` gives the
step-(a) owner formula `u = Aᵀ (p, q) + d`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_primal_point_toLp_apply
    (d : MatrixSpace m n) (p : HorizontalSpace m n) (q : VerticalSpace m n)
    (i : Fin m) (j : Fin n) :
    two_dimensional_tv_l1_fdpg_primal_point d (toLp 2 (p, q)) i j =
      Aᵀ[m, n] (toLp 2 (p, q)) i j + d i j := by
  -- This is the same entrywise expansion specialized to the canonical `toLp 2` pair.
  rfl

/-- The owner-level step-(b) dual update: starting from the current extrapolated dual pair
`z = (p, q)`, subtract `(1 / 8) A u` and add the anisotropic proximal correction of the shifted
dual residual `A u - 8 z`. -/
def two_dimensional_tv_l1_fdpg_dual_update
    (lam : PosReal) (u : MatrixSpace m n) (z : DualSpace m n) : DualSpace m n :=
  let Au := A[m, n] u
  let shifted := Au - (8 : ℝ) • z
  z - (1 / 8 : ℝ) • Au +
    (1 / 8 : ℝ) •
      two_dimensional_total_variation_anisotropic_prox_point ((8 : ℝ) * lam)
        shifted.fst shifted.snd

/-- Evaluating the first coordinate of the owner-level dual update gives the step-(b) formula for
the horizontal block `p^(k+1)`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_dual_update_fst_apply
    (lam : PosReal) (u : MatrixSpace m n) (z : DualSpace m n) (i : Fin m) (j : Fin (n - 1)) :
    (two_dimensional_tv_l1_fdpg_dual_update lam u z).fst i j =
      z.fst i j - (1 / 8 : ℝ) * (A[m, n] u).fst i j +
        (1 / 8 : ℝ) *
          𝒯[(8 : ℝ) * lam] ((A[m, n] u).fst i j - 8 * z.fst i j) := by
  -- Unfold the owner-level update and project the horizontal component entrywise.
  simp [two_dimensional_tv_l1_fdpg_dual_update]

/-- Evaluating the second coordinate of the owner-level dual update gives the step-(b) formula
for the vertical block `q^(k+1)`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_dual_update_snd_apply
    (lam : PosReal) (u : MatrixSpace m n) (z : DualSpace m n) (i : Fin (m - 1)) (j : Fin n) :
    (two_dimensional_tv_l1_fdpg_dual_update lam u z).snd i j =
      z.snd i j - (1 / 8 : ℝ) * (A[m, n] u).snd i j +
        (1 / 8 : ℝ) *
          𝒯[(8 : ℝ) * lam] ((A[m, n] u).snd i j - 8 * z.snd i j) := by
  -- Unfold the owner-level update and project the vertical component entrywise.
  simp [two_dimensional_tv_l1_fdpg_dual_update]

/-
Algorithm 12.12 is `source-facing`: the public owners are the primal point `u^k`, the dual
iterate `z^k = (p^k, q^k)`, and the extrapolated dual pair `\tilde z^k`.

The scalar acceleration law is `core/canonical`: the repository already owns the Chapter 10
momentum sequence `fista_momentum_sequence`, the standard accelerated owner `FISTAState`, and the
extrapolation operator `fista_extrapolated_point`. The private recursion here is therefore the
smallest source-faithful bridge/view built on that canonical owner: state `k` stores
`(z^k, z^(k+1), t_k)`, so `xCur` is the next dual iterate and
`fista_extrapolated_point (state k)` is the source-facing extrapolated pair `\tilde z^(k+1)`,
while the initialization keeps `\tilde z⁰ = z⁰`. -/

/-- The initialized FISTA bridge state carrying `(z⁰, z¹, t₀)`. -/
private def two_dimensional_tv_l1_fdpg_initial_state
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    FISTAState (DualSpace m n) :=
  let z0 := toLp 2 (p0, q0)
  let u0 := two_dimensional_tv_l1_fdpg_primal_point d z0
  let z1 := two_dimensional_tv_l1_fdpg_dual_update lam u0 z0
  { xPrev := z0
    xCur := z1
    tCur := fista_momentum_sequence 0 }

/-- One concrete FDPG step on the canonical FISTA bridge state. -/
private def two_dimensional_tv_l1_fdpg_state_update
    (d : MatrixSpace m n) (lam : PosReal) (state : FISTAState (DualSpace m n)) :
    FISTAState (DualSpace m n) :=
  let zExtrap := fista_extrapolated_point state
  let u := two_dimensional_tv_l1_fdpg_primal_point d zExtrap
  let zNext := two_dimensional_tv_l1_fdpg_dual_update lam u zExtrap
  { xPrev := state.xCur
    xCur := zNext
    tCur := fista_momentum_update state.tCur }

/-- The private recursive FISTA bridge state whose `xPrev`/`xCur` fields encode consecutive
dual iterates. -/
private def two_dimensional_tv_l1_fdpg_state
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    ℕ → FISTAState (DualSpace m n)
  | 0 => two_dimensional_tv_l1_fdpg_initial_state d lam p0 q0
  | k + 1 =>
      two_dimensional_tv_l1_fdpg_state_update d lam
        (two_dimensional_tv_l1_fdpg_state d lam p0 q0 k)

/-- Unfolding the private recursion at a successor index gives the concrete one-step state
update. -/
private theorem two_dimensional_tv_l1_fdpg_state_succ
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) :
    two_dimensional_tv_l1_fdpg_state d lam p0 q0 (k + 1) =
      two_dimensional_tv_l1_fdpg_state_update d lam
        (two_dimensional_tv_l1_fdpg_state d lam p0 q0 k) :=
  rfl

/-- The momentum field of the private accelerated state follows the canonical FISTA sequence. -/
private theorem two_dimensional_tv_l1_fdpg_state_tCur_eq
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) :
    (two_dimensional_tv_l1_fdpg_state d lam p0 q0 k).tCur =
      fista_momentum_sequence k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp [two_dimensional_tv_l1_fdpg_state, two_dimensional_tv_l1_fdpg_state_update,
        fista_momentum_sequence_succ, ih]

/-- For Algorithm 12.12, the canonical dual-pair sequence for the two-dimensional
total-variation denoising problem
`min_x { (1 / 2) ‖x - d‖_F^2 + λ TV_l1(x) }`, given initial dual blocks
`\tilde p⁰ = p⁰ = p0 ∈ ℝ^(m × (n - 1))`,
`\tilde q⁰ = q⁰ = q0 ∈ ℝ^((m - 1) × n)`, positive regularization parameter `λ` encoded by
`lam : PosReal`, and `t₀ = 1`, the canonical dual-pair sequence
`z^k = (p^k, q^k)` generates the concrete two-dimensional FDPG recursion, with the auxiliary
primal sequence and extrapolated pair recovered by the companion declarations below, while the
acceleration scalars are still the canonical Chapter 10 momentum sequence. -/
def two_dimensional_tv_l1_fdpg_z
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    ℕ → DualSpace m n
  | 0 => toLp 2 (p0, q0)
  | k + 1 => (two_dimensional_tv_l1_fdpg_state d lam p0 q0 k).xCur

/-- The canonical extrapolated dual-pair sequence
`\tilde z^k = (\tilde p^k, \tilde q^k)` in the `L²` product owner. -/
def two_dimensional_tv_l1_fdpg_zExtrap
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    ℕ → DualSpace m n
  | 0 => toLp 2 (p0, q0)
  | k + 1 => fista_extrapolated_point (two_dimensional_tv_l1_fdpg_state d lam p0 q0 k)

/-- The horizontal dual iterate sequence `p^k`, obtained by projecting the paired dual sequence
`z^k`. -/
def two_dimensional_tv_l1_fdpg_p
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    ℕ → HorizontalSpace m n :=
  fun k ↦ (two_dimensional_tv_l1_fdpg_z d lam p0 q0 k).fst

/-- The vertical dual iterate sequence `q^k`, obtained by projecting the paired dual sequence
`z^k`. -/
def two_dimensional_tv_l1_fdpg_q
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    ℕ → VerticalSpace m n :=
  fun k ↦ (two_dimensional_tv_l1_fdpg_z d lam p0 q0 k).snd

/-- The extrapolated horizontal sequence `\tilde p^k`, obtained by projecting
`\tilde z^k`. -/
def two_dimensional_tv_l1_fdpg_pExtrap
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    ℕ → HorizontalSpace m n :=
  fun k ↦ (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k).fst

/-- The extrapolated vertical sequence `\tilde q^k`, obtained by projecting
`\tilde z^k`. -/
def two_dimensional_tv_l1_fdpg_qExtrap
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    ℕ → VerticalSpace m n :=
  fun k ↦ (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k).snd

/-- The auxiliary primal sequence `u^k = Aᵀ (\tilde p^k, \tilde q^k) + d` derived from the
two-dimensional TV-L1 FDPG iterates. -/
def two_dimensional_tv_l1_fdpg_u
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    ℕ → MatrixSpace m n :=
  fun k ↦
    two_dimensional_tv_l1_fdpg_primal_point d
      (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k)

/-- Helper for Algorithm 12.12: the previous iterate stored in the private FISTA bridge state is
exactly the public dual-pair sequence `z^k`. -/
private theorem two_dimensional_tv_l1_fdpg_state_xPrev_eq
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) :
    (two_dimensional_tv_l1_fdpg_state d lam p0 q0 k).xPrev =
      two_dimensional_tv_l1_fdpg_z d lam p0 q0 k := by
  -- Split on the index so both the initialized and recursive state expose the same owner.
  cases k <;> rfl

section

/-- The canonical dual-pair sequence starts from `z⁰ = (p0, q0)`. -/
theorem two_dimensional_tv_l1_fdpg_z_zero
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    two_dimensional_tv_l1_fdpg_z d lam p0 q0 0 = toLp 2 (p0, q0) := by
  -- Read back the initialized public owner.
  rfl

/-- The horizontal dual sequence starts at the prescribed initialization `p⁰ = p0`. -/
theorem two_dimensional_tv_l1_fdpg_p_zero
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    two_dimensional_tv_l1_fdpg_p d lam p0 q0 0 = p0 := by
  -- Project the initialized dual pair to its horizontal coordinate.
  simp [two_dimensional_tv_l1_fdpg_p, two_dimensional_tv_l1_fdpg_z_zero]

/-- The vertical dual sequence starts at the prescribed initialization `q⁰ = q0`. -/
theorem two_dimensional_tv_l1_fdpg_q_zero
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    two_dimensional_tv_l1_fdpg_q d lam p0 q0 0 = q0 := by
  -- Project the initialized dual pair to its vertical coordinate.
  simp [two_dimensional_tv_l1_fdpg_q, two_dimensional_tv_l1_fdpg_z_zero]

/-- The canonical extrapolated dual-pair sequence starts from `\tilde z⁰ = (p0, q0)`. -/
theorem two_dimensional_tv_l1_fdpg_zExtrap_zero
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 0 = toLp 2 (p0, q0) := by
  -- Read back the initialized extrapolated owner.
  rfl

/-- The extrapolated horizontal sequence satisfies `\tilde p⁰ = p0`. -/
theorem two_dimensional_tv_l1_fdpg_pExtrap_zero
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    two_dimensional_tv_l1_fdpg_pExtrap d lam p0 q0 0 = p0 := by
  -- Project the initialized extrapolated pair to its horizontal coordinate.
  simp [two_dimensional_tv_l1_fdpg_pExtrap, two_dimensional_tv_l1_fdpg_zExtrap_zero]

/-- The extrapolated vertical sequence satisfies `\tilde q⁰ = q0`. -/
theorem two_dimensional_tv_l1_fdpg_qExtrap_zero
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    two_dimensional_tv_l1_fdpg_qExtrap d lam p0 q0 0 = q0 := by
  -- Project the initialized extrapolated pair to its vertical coordinate.
  simp [two_dimensional_tv_l1_fdpg_qExtrap, two_dimensional_tv_l1_fdpg_zExtrap_zero]

/-- At every iteration `k`, the auxiliary image satisfies the owner-level step-(a) formula
`u^k = Aᵀ \tilde z^k + d`. -/
theorem two_dimensional_tv_l1_fdpg_u_eq
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) :
    two_dimensional_tv_l1_fdpg_u d lam p0 q0 k =
      Aᵀ[m, n] (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k) + d := by
  -- Unfold the public auxiliary sequence to the owner-level primal-point definition.
  rfl

/-- Evaluating the auxiliary image at `(i, j)` gives the step-(a) matrix-entry formula. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_u_apply
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) (i : Fin m) (j : Fin n) :
    two_dimensional_tv_l1_fdpg_u d lam p0 q0 k i j =
      Aᵀ[m, n] (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k) i j + d i j := by
  -- Evaluate the auxiliary owner entrywise after unfolding the public recursion.
  simp [two_dimensional_tv_l1_fdpg_u]

/-- At every iteration `k`, the next dual pair is obtained from the owner-level step-(b) update
evaluated at `u^k` and `\tilde z^k`. -/
theorem two_dimensional_tv_l1_fdpg_z_update
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) :
    two_dimensional_tv_l1_fdpg_z d lam p0 q0 (k + 1) =
      two_dimensional_tv_l1_fdpg_dual_update lam
        (two_dimensional_tv_l1_fdpg_u d lam p0 q0 k)
        (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k) := by
  -- Split on the step index so the initialized and recursive state expose the same update term.
  cases k <;> rfl

/-- At every iteration `k`, the next horizontal dual iterate is the first coordinate of the
owner-level step-(b) update. -/
theorem two_dimensional_tv_l1_fdpg_p_update
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) :
    two_dimensional_tv_l1_fdpg_p d lam p0 q0 (k + 1) =
      (two_dimensional_tv_l1_fdpg_dual_update lam
        (two_dimensional_tv_l1_fdpg_u d lam p0 q0 k)
        (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k)).fst := by
  -- Project the paired owner-level update to the horizontal coordinate.
  simp [two_dimensional_tv_l1_fdpg_p, two_dimensional_tv_l1_fdpg_z_update]

/-- Evaluating the horizontal step-(b) recursion gives the source-facing update formula for the
entry `p_(i,j)^(k+1)` in terms of the Proposition 12.4 horizontal difference of `u^k`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_p_update_apply
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) (i : Fin m) (j : Fin (n - 1)) :
    two_dimensional_tv_l1_fdpg_p d lam p0 q0 (k + 1) i j =
      two_dimensional_tv_l1_fdpg_pExtrap d lam p0 q0 k i j -
        (1 / 8 : ℝ) * (A[m, n] (two_dimensional_tv_l1_fdpg_u d lam p0 q0 k)).fst i j +
        (1 / 8 : ℝ) *
          𝒯[(8 : ℝ) * lam]
            ((A[m, n] (two_dimensional_tv_l1_fdpg_u d lam p0 q0 k)).fst i j -
              8 * two_dimensional_tv_l1_fdpg_pExtrap d lam p0 q0 k i j) := by
  -- Rewrite to the paired update and read off the first-coordinate entrywise formula.
  rw [two_dimensional_tv_l1_fdpg_p_update]
  exact two_dimensional_tv_l1_fdpg_dual_update_fst_apply
    (m := m) (n := n) lam
    (two_dimensional_tv_l1_fdpg_u d lam p0 q0 k)
    (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k) i j

/-- At every iteration `k`, the next vertical dual iterate is the second coordinate of the
owner-level step-(b) update. -/
theorem two_dimensional_tv_l1_fdpg_q_update
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) :
    two_dimensional_tv_l1_fdpg_q d lam p0 q0 (k + 1) =
      (two_dimensional_tv_l1_fdpg_dual_update lam
        (two_dimensional_tv_l1_fdpg_u d lam p0 q0 k)
        (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k)).snd := by
  -- Project the paired owner-level update to the vertical coordinate.
  simp [two_dimensional_tv_l1_fdpg_q, two_dimensional_tv_l1_fdpg_z_update]

/-- Evaluating the vertical step-(b) recursion gives the source-facing update formula for the
entry `q_(i,j)^(k+1)` in terms of the Proposition 12.4 vertical difference of `u^k`. -/
@[simp] theorem two_dimensional_tv_l1_fdpg_q_update_apply
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) (i : Fin (m - 1)) (j : Fin n) :
    two_dimensional_tv_l1_fdpg_q d lam p0 q0 (k + 1) i j =
      two_dimensional_tv_l1_fdpg_qExtrap d lam p0 q0 k i j -
        (1 / 8 : ℝ) * (A[m, n] (two_dimensional_tv_l1_fdpg_u d lam p0 q0 k)).snd i j +
        (1 / 8 : ℝ) *
          𝒯[(8 : ℝ) * lam]
            ((A[m, n] (two_dimensional_tv_l1_fdpg_u d lam p0 q0 k)).snd i j -
              8 * two_dimensional_tv_l1_fdpg_qExtrap d lam p0 q0 k i j) := by
  -- Rewrite to the paired update and read off the second-coordinate entrywise formula.
  rw [two_dimensional_tv_l1_fdpg_q_update]
  exact two_dimensional_tv_l1_fdpg_dual_update_snd_apply
    (m := m) (n := n) lam
    (two_dimensional_tv_l1_fdpg_u d lam p0 q0 k)
    (two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 k) i j

/-- Algorithm 12.12: at every iteration `k`, the extrapolated successor satisfies the textbook
step-(d) update with the canonical FISTA momentum sequence. -/
theorem two_dimensional_tv_l1_fdpg_zExtrap_succ
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) :
    two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 (k + 1) =
      two_dimensional_tv_l1_fdpg_z d lam p0 q0 (k + 1) +
        ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
          (two_dimensional_tv_l1_fdpg_z d lam p0 q0 (k + 1) -
            two_dimensional_tv_l1_fdpg_z d lam p0 q0 k) := by
  -- Route correction: transport the canonical Chapter 10 extrapolation formula through the
  -- private FDPG bridge instead of redoing the momentum algebra from coordinates.
  simp [two_dimensional_tv_l1_fdpg_zExtrap, two_dimensional_tv_l1_fdpg_z,
    two_dimensional_tv_l1_fdpg_state_tCur_eq, two_dimensional_tv_l1_fdpg_state_xPrev_eq,
    fista_extrapolated_point_eq, fista_momentum_sequence_succ]

/-- At every iteration `k`, the extrapolated horizontal successor satisfies the textbook
step-(d) update with the canonical FISTA momentum sequence. -/
theorem two_dimensional_tv_l1_fdpg_pExtrap_succ
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) :
    two_dimensional_tv_l1_fdpg_pExtrap d lam p0 q0 (k + 1) =
      two_dimensional_tv_l1_fdpg_p d lam p0 q0 (k + 1) +
        ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
          (two_dimensional_tv_l1_fdpg_p d lam p0 q0 (k + 1) -
            two_dimensional_tv_l1_fdpg_p d lam p0 q0 k) := by
  -- Project the paired extrapolation identity to the horizontal coordinate.
  simpa [two_dimensional_tv_l1_fdpg_pExtrap, two_dimensional_tv_l1_fdpg_p] using
    congrArg (fun z : DualSpace m n ↦ z.fst)
      (two_dimensional_tv_l1_fdpg_zExtrap_succ d lam p0 q0 k)

/-- At every iteration `k`, the extrapolated vertical successor satisfies the textbook
step-(d) update with the canonical FISTA momentum sequence. -/
theorem two_dimensional_tv_l1_fdpg_qExtrap_succ
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n)
    (k : ℕ) :
    two_dimensional_tv_l1_fdpg_qExtrap d lam p0 q0 (k + 1) =
      two_dimensional_tv_l1_fdpg_q d lam p0 q0 (k + 1) +
        ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
          (two_dimensional_tv_l1_fdpg_q d lam p0 q0 (k + 1) -
            two_dimensional_tv_l1_fdpg_q d lam p0 q0 k) := by
  -- Project the paired extrapolation identity to the vertical coordinate.
  simpa [two_dimensional_tv_l1_fdpg_qExtrap, two_dimensional_tv_l1_fdpg_q] using
    congrArg (fun z : DualSpace m n ↦ z.snd)
      (two_dimensional_tv_l1_fdpg_zExtrap_succ d lam p0 q0 k)

/-- The first extrapolated dual pair satisfies `\tilde z¹ = z¹`. -/
theorem two_dimensional_tv_l1_fdpg_zExtrap_one
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    two_dimensional_tv_l1_fdpg_zExtrap d lam p0 q0 1 =
      two_dimensional_tv_l1_fdpg_z d lam p0 q0 1 := by
  -- Specialize the successor extrapolation law at `k = 0`, where the coefficient vanishes.
  simpa [fista_momentum_sequence_zero] using
    (two_dimensional_tv_l1_fdpg_zExtrap_succ d lam p0 q0 0)

/-- The first extrapolated horizontal iterate satisfies `\tilde p¹ = p¹`. -/
theorem two_dimensional_tv_l1_fdpg_pExtrap_one
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    two_dimensional_tv_l1_fdpg_pExtrap d lam p0 q0 1 =
      two_dimensional_tv_l1_fdpg_p d lam p0 q0 1 := by
  -- Specialize the horizontal successor extrapolation law at `k = 0`.
  simpa [fista_momentum_sequence_zero] using
    (two_dimensional_tv_l1_fdpg_pExtrap_succ d lam p0 q0 0)

/-- The first extrapolated vertical iterate satisfies `\tilde q¹ = q¹`. -/
theorem two_dimensional_tv_l1_fdpg_qExtrap_one
    (d : MatrixSpace m n) (lam : PosReal) (p0 : HorizontalSpace m n) (q0 : VerticalSpace m n) :
    two_dimensional_tv_l1_fdpg_qExtrap d lam p0 q0 1 =
      two_dimensional_tv_l1_fdpg_q d lam p0 q0 1 := by
  -- Specialize the vertical successor extrapolation law at `k = 0`.
  simpa [fista_momentum_sequence_zero] using
    (two_dimensional_tv_l1_fdpg_qExtrap_succ d lam p0 q0 0)

end

end
