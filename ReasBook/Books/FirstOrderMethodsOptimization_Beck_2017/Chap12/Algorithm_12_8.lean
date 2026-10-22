/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_7.ProjectionStep
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_8.Duplication

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open scoped BigOperators

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {p : ℕ}

/- Algorithm 12.8 is `source-facing` in the projection-onto-an-intersection subsection.

Domain sampling against nearby project owners identifies the owner layers as follows.
- `source-facing`: the named iterate families `u^k`, `y^k`, and `w^k`;
- `core/canonical`: `DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1`,
  `finite_intersection_projection_primal_point`, and
  `finite_intersection_projection_dual_update` from Algorithm 12.7 for the admissible parameter
  and the shared step-(a) / step-(b) primitives, together with `fista_momentum_sequence` and
  `fista_momentum_update` from Algorithm 10.13 for the scalar recurrence
  `t_(k+1) = (1 + √(1 + 4 t_k²)) / 2`;
- `bridge/view`: the private recursive state carrying the current iterate data and the current
  momentum scalar, while the source momentum clause is exposed through the equivalent public pair
  `w¹ = y¹` and
  `w^(k+2) = y^(k+2) + (((t_(k+1) - 1) / t_(k+2)) • (y^(k+2) - y^(k+1)))`.

The primitive data are therefore the nonempty closed convex family `C`, the admissible parameter
`L`, the point `d`, and the initialization `y0 : E^p`. The source item is an explicit recursive
algorithm with named sequences `u^k`, `y^k`, `w^k`, and `t_k`, so the public API keeps the
genuinely new iterate families `u^k`, `y^k`, and `w^k` visible. As in the nearby Chapter 12 FDPG
files, the scalar sequence `t_k` is only derived API, already owned upstream by
`fista_momentum_sequence`, so this file reuses that owner directly on theorem surfaces instead of
introducing a parallel public alias. -/

/- The finite-intersection FDPG acceleration scalars use the canonical Chapter 10 FISTA momentum
sequence. -/
#check fista_momentum_sequence

/- Its initialization and recursion are reused directly on the FDPG theorem surface. -/
#check fista_momentum_sequence_zero
#check fista_momentum_sequence_succ

private structure FiniteIntersectionFDPGState (E : Type u) (p : ℕ) where
  yCur : Fin p → E
  wCur : Fin p → E
  tCur : ℝ

private def finite_intersection_fdpg_initial_state
    (y0 : Fin p → E) : FiniteIntersectionFDPGState E p :=
  { yCur := y0
    wCur := y0
    tCur := 1 }

section

variable (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty)
variable (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i))
variable (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1)
variable (d : E) (y0 : Fin p → E)

private def finite_intersection_fdpg_state_update
    (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty)
    (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i))
    (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1)
    (d : E)
    (state : FiniteIntersectionFDPGState E p) : FiniteIntersectionFDPGState E p :=
  let yNext :=
    finite_intersection_projection_dual_update
      C hC_nonempty hC_closed hC_convex L
      (finite_intersection_projection_primal_point d state.wCur) state.wCur
  let tNext := fista_momentum_update state.tCur
  { yCur := yNext
    wCur := yNext + ((state.tCur - 1) / tNext) • (yNext - state.yCur)
    tCur := tNext }

private def finite_intersection_fdpg_state
    (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty)
    (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i))
    (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1)
    (d : E) (y0 : Fin p → E) : ℕ → FiniteIntersectionFDPGState E p
  | 0 => finite_intersection_fdpg_initial_state y0
  | k + 1 =>
      finite_intersection_fdpg_state_update C hC_nonempty hC_closed hC_convex L d
        (finite_intersection_fdpg_state C hC_nonempty hC_closed hC_convex L d y0 k)

private theorem finite_intersection_fdpg_state_tCur_eq
    (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty)
    (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i))
    (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1)
    (d : E) (y0 : Fin p → E)
    (k : ℕ) :
    (finite_intersection_fdpg_state C hC_nonempty hC_closed hC_convex L d y0 k).tCur =
      fista_momentum_sequence k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp [finite_intersection_fdpg_state, finite_intersection_fdpg_state_update,
        fista_momentum_sequence_succ, ih]

/-- Algorithm 12.8: for nonempty closed convex sets `C₁, …, C_p`, an admissible constant
parameter `L ≥ p`, a point `d ∈ E`, and an initialization `w⁰ = y⁰ = y0 ∈ E^p`, the iterate
families below generate the finite-intersection FDPG recursion with
`u^k = ∑ᵢ wᵢ^k + d`,
`yᵢ^(k+1) = wᵢ^k - (1 / L) u^k + (1 / L) P_{Cᵢ}(u^k - L wᵢ^k)`,
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`,
and the source momentum clause is exposed in the equivalent public form
`w¹ = y¹` and
`w^(k+2) = y^(k+2) + (((t_(k+1) - 1) / t_(k+2)) • (y^(k+2) - y^(k+1)))`. -/
def finite_intersection_fdpg_y
    : ℕ → Fin p → E :=
  fun k ↦ (finite_intersection_fdpg_state C hC_nonempty hC_closed hC_convex L d y0 k).yCur

/-- The finite-intersection FDPG extrapolated sequence `w^k ∈ E^p`. -/
def finite_intersection_fdpg_w
    : ℕ → Fin p → E :=
  fun k ↦ (finite_intersection_fdpg_state C hC_nonempty hC_closed hC_convex L d y0 k).wCur

/-- The finite-intersection FDPG primal sequence `u^k = ∑ᵢ wᵢ^k + d`. -/
def finite_intersection_fdpg_u
    : ℕ → E :=
  fun k ↦ finite_intersection_projection_primal_point d
    (finite_intersection_fdpg_w C hC_nonempty hC_closed hC_convex L d y0 k)

end

section

variable (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty)
variable (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i))
variable (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1)
variable (d : E) (y0 : Fin p → E)

/-- The finite-intersection FDPG sequence starts from `y⁰ = y0`. -/
@[simp] theorem finite_intersection_fdpg_y_zero :
    finite_intersection_fdpg_y C hC_nonempty hC_closed hC_convex L d y0 0 = y0 :=
  rfl

/-- The finite-intersection FDPG extrapolated sequence starts from `w⁰ = y⁰ = y0`. -/
@[simp] theorem finite_intersection_fdpg_w_zero :
    finite_intersection_fdpg_w C hC_nonempty hC_closed hC_convex L d y0 0 = y0 :=
  rfl

/-- Each finite-intersection FDPG primal iterate satisfies `u^k = ∑ᵢ wᵢ^k + d`. -/
theorem finite_intersection_fdpg_u_eq (k : ℕ) :
    finite_intersection_fdpg_u C hC_nonempty hC_closed hC_convex L d y0 k =
      (∑ i, finite_intersection_fdpg_w C hC_nonempty hC_closed hC_convex L d y0 k i) + d :=
  rfl

/-- Each successor iterate is obtained by applying the shared finite-intersection projection
update owner to `u^k` and `w^k`. -/
theorem finite_intersection_fdpg_y_succ (k : ℕ) :
    finite_intersection_fdpg_y C hC_nonempty hC_closed hC_convex L d y0 (k + 1) =
      finite_intersection_projection_dual_update
        C hC_nonempty hC_closed hC_convex L
        (finite_intersection_fdpg_u C hC_nonempty hC_closed hC_convex L d y0 k)
        (finite_intersection_fdpg_w C hC_nonempty hC_closed hC_convex L d y0 k) :=
  rfl

/-- For each coordinate `i`, the successor iterate `yᵢ^(k+1)` is given by the textbook FDPG
projection formula based on `u^k` and `wᵢ^k`. -/
theorem finite_intersection_fdpg_y_succ_apply (k : ℕ) (i : Fin p) :
    finite_intersection_fdpg_y C hC_nonempty hC_closed hC_convex L d y0 (k + 1) i =
      finite_intersection_fdpg_w C hC_nonempty hC_closed hC_convex L d y0 k i -
        (1 / L : ℝ) • finite_intersection_fdpg_u C hC_nonempty hC_closed hC_convex L d y0 k +
        (1 / L : ℝ) •
          Pp[C i, hC_nonempty i, hC_closed i, hC_convex i]
            (finite_intersection_fdpg_u C hC_nonempty hC_closed hC_convex L d y0 k -
              (L : ℝ) • finite_intersection_fdpg_w C hC_nonempty hC_closed hC_convex L d y0 k i) :=
    by
  rw [finite_intersection_fdpg_y_succ]
  rfl

/-- The first extrapolated iterate satisfies `w¹ = y¹`. -/
theorem finite_intersection_fdpg_w_one :
    finite_intersection_fdpg_w C hC_nonempty hC_closed hC_convex L d y0 1 =
      finite_intersection_fdpg_y C hC_nonempty hC_closed hC_convex L d y0 1 := by
  simp [finite_intersection_fdpg_w, finite_intersection_fdpg_y, finite_intersection_fdpg_state,
    finite_intersection_fdpg_state_update, finite_intersection_fdpg_initial_state]

/-- For every `k`, the later extrapolated iterates satisfy the shifted textbook recursion
`w^(k+2) = y^(k+2) + (((t_(k+1) - 1) / t_(k+2)) • (y^(k+2) - y^(k+1)))`, where `t_k` is the
canonical Chapter 10 FISTA momentum sequence. -/
theorem finite_intersection_fdpg_w_succ_succ (k : ℕ) :
    finite_intersection_fdpg_w C hC_nonempty hC_closed hC_convex L d y0 (k + 2) =
      finite_intersection_fdpg_y C hC_nonempty hC_closed hC_convex L d y0 (k + 2) +
        ((fista_momentum_sequence (k + 1) - 1) / fista_momentum_sequence (k + 2)) •
          (finite_intersection_fdpg_y C hC_nonempty hC_closed hC_convex L d y0 (k + 2) -
            finite_intersection_fdpg_y C hC_nonempty hC_closed hC_convex L d y0 (k + 1)) := by
  simp [finite_intersection_fdpg_w, finite_intersection_fdpg_y, finite_intersection_fdpg_state,
    finite_intersection_fdpg_state_update, finite_intersection_fdpg_state_tCur_eq,
    fista_momentum_sequence_succ]

end

end
