/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/- Algorithm 12.3 supplies the chapter's `core/canonical` accelerated dual-trajectory owner: the
textbook objects are the dual iterates `y^k` and the extrapolated points `w^k`, while the
acceleration scalars are already owned upstream by the canonical Chapter 10 sequence
`fista_momentum_sequence`.

Domain sampling against nearby project owners identifies:
- `dual_based_proximal_gradient_dual_step` from Algorithm 12.1 as the canonical owner for the
  set-valued dual proximal step `y^(k+1) ∈ prox[(1 / L) G] (w^k - (1 / L) ∇F(w^k))`;
- `fista_momentum_sequence` from Algorithm 10.13 as the canonical owner for the scalar recursion
  `t₀ = 1`, `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`;
- `is_mfista_trajectory` from Algorithm 10.11 as the chapter's trajectory-owner pattern for
  accelerated methods stated directly on named iterate families rather than through a chosen
  recursive implementation package.

There is no exact upstream owner for the accelerated dual recursion based at the extrapolated
points `w^k`, so the local structure below is still the right owner level. Its primitive data are
only the explicit sequences `y` and `w`; the scalar momentum data are derived API, already
determined by `fista_momentum_sequence`, and any hidden bookkeeping for `t_(-1)` should not be
a public owner. -/

/-- Algorithm 12.3: the sequences `(y^k, w^k, t_k)` follow the fast dual proximal-gradient
method in dual representation when `L` is an admissible constant stepsize parameter, the initial
conditions are `y⁰ = w⁰ = y0`, each `y^(k+1)` lies in the Chapter 12 dual proximal step set based
at `w^k`, the acceleration scalars are the canonical values `t_k = fista_momentum_sequence k`,
and the textbook extrapolation step
`w^(k+1) = y^(k+1) + (((t_k - 1) / t_(k+1)) • (y^(k+1) - y^k))` is recorded directly by the
momentum field. -/
structure IsFastDualProximalGradientDualTrajectory
    (A : E →L[ℝ] V) (σ : PosReal) (G : V → EReal) (gradF : V → V)
    (L : DualBasedProximalGradientDualStepsizeParameter A σ) (y0 : V) (y w : ℕ → V) : Prop where
  /-- The initial dual iterate is the prescribed point `y0`. -/
  y_zero : y 0 = y0
  /-- The extrapolated sequence starts from the same prescribed point `y0`. -/
  w_zero : w 0 = y0
  /-- At each step, the next dual iterate lies in the Chapter 12 dual proximal update set based
  at `w^k`. -/
  dual_step (k : ℕ) :
    y (k + 1) ∈ dual_based_proximal_gradient_dual_step G gradF L (w k)
  /-- For every `k`, the extrapolated iterate satisfies the literal textbook momentum recursion. -/
  momentum_step (k : ℕ) :
    w (k + 1) =
      y (k + 1) +
        ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
          (y (k + 1) - y k)

namespace IsFastDualProximalGradientDualTrajectory

variable {A : E →L[ℝ] V} {σ : PosReal} {G : V → EReal} {gradF : V → V}
variable {L : DualBasedProximalGradientDualStepsizeParameter A σ} {y0 : V} {y w : ℕ → V}

/-- The primitive per-iteration data of an Algorithm 12.3 trajectory. -/
theorem step
    (htraj : IsFastDualProximalGradientDualTrajectory A σ G gradF L y0 y w) (k : ℕ) :
    y (k + 1) ∈ dual_based_proximal_gradient_dual_step G gradF L (w k) ∧
      w (k + 1) =
        y (k + 1) +
          ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
            (y (k + 1) - y k) := by
  exact ⟨htraj.dual_step k, htraj.momentum_step k⟩

/-- The literal Algorithm 12.3 momentum update family is equivalent to the same family split
into its base case `w¹ = y¹` and its correctly reindexed successor clause. -/
theorem sourceMomentum_iff_shifted :
    (∀ k : ℕ,
        w (k + 1) =
          y (k + 1) +
            ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
              (y (k + 1) - y k)) ↔
      w 1 = y 1 ∧
        ∀ k : ℕ,
          w (k + 2) =
            y (k + 2) +
              ((fista_momentum_sequence (k + 1) - 1) /
                  fista_momentum_sequence (k + 2)) •
                (y (k + 2) - y (k + 1)) := by
  constructor
  · intro hsource
    refine ⟨?_, ?_⟩
    · simpa [fista_momentum_sequence_zero] using hsource 0
    · intro k
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsource (k + 1)
  · rintro ⟨hfirst, hsucc⟩ k
    cases k with
    | zero =>
        simpa [fista_momentum_sequence_zero] using hfirst
    | succ k =>
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsucc k

/-- Any Algorithm 12.3 trajectory satisfies the first extrapolation identity `w¹ = y¹`. -/
theorem first_momentum_step
    (htraj : IsFastDualProximalGradientDualTrajectory A σ G gradF L y0 y w) :
    w 1 = y 1 := by
  exact ((sourceMomentum_iff_shifted).1 htraj.momentum_step).1

/-- Any Algorithm 12.3 trajectory satisfies the correctly reindexed successor form of the source
momentum clause. -/
theorem momentumStepSucc
    (htraj : IsFastDualProximalGradientDualTrajectory A σ G gradF L y0 y w) (k : ℕ) :
    w (k + 2) =
      y (k + 2) +
        ((fista_momentum_sequence (k + 1) - 1) /
            fista_momentum_sequence (k + 2)) •
          (y (k + 2) - y (k + 1)) := by
  exact ((sourceMomentum_iff_shifted).1 htraj.momentum_step).2 k

/-- Construct the core Algorithm 12.3 trajectory owner from the literal source momentum
recursion. -/
def ofSourceMomentum
    (hy_zero : y 0 = y0)
    (hw_zero : w 0 = y0)
    (hdual_step :
      ∀ k : ℕ, y (k + 1) ∈ dual_based_proximal_gradient_dual_step G gradF L (w k))
    (hsource_momentum :
      ∀ k : ℕ,
        w (k + 1) =
          y (k + 1) +
            ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
              (y (k + 1) - y k)) :
    IsFastDualProximalGradientDualTrajectory A σ G gradF L y0 y w :=
  { y_zero := hy_zero
    w_zero := hw_zero
    dual_step := hdual_step
    momentum_step := hsource_momentum }

/-- Any Algorithm 12.3 trajectory satisfies the literal source momentum formula
`w^(k+1) = y^(k+1) + (((t_k - 1) / t_(k+1)) • (y^(k+1) - y^k))`. -/
theorem momentumStepSource
    (htraj : IsFastDualProximalGradientDualTrajectory A σ G gradF L y0 y w) (k : ℕ) :
    w (k + 1) =
      y (k + 1) +
        ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
          (y (k + 1) - y k) :=
  htraj.momentum_step k

end IsFastDualProximalGradientDualTrajectory

end
