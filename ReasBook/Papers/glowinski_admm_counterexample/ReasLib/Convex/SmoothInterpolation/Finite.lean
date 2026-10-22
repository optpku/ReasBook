/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Convex.SmoothInterpolation.Conjugate
public import Mathlib.Topology.Order.Lattice

@[expose] public section

open Set Filter
open scoped Topology RealInnerProductSpace

namespace SmoothInterpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Finite maxima of affine functions remain convex. -/
theorem convexOn_affine_max (a : ι → E) (b : ι → ℝ) :
    ConvexOn ℝ univ (fun s ↦ Finset.univ.sup' Finset.univ_nonempty
      (fun i ↦ ⟪s, a i⟫ + b i)) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy r t hr ht hrt
  apply Finset.sup'_le
  intro i hi
  have hx' := Finset.le_sup' (fun i ↦ ⟪x, a i⟫ + b i) (Finset.mem_univ i)
  have hy' := Finset.le_sup' (fun i ↦ ⟪y, a i⟫ + b i) (Finset.mem_univ i)
  have h1 := mul_le_mul_of_nonneg_left hx' hr
  have h2 := mul_le_mul_of_nonneg_left hy' ht
  have h3 := congrArg (fun c : ℝ ↦ c * b i) hrt
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  nlinarith only [h1, h2, h3]

/-- The finite maximum of interpolation quadratics, expressed as a quadratic
plus a finite maximum of affine functions. -/
noncomputable def quadraticEnvelope (z p : ι → E) (ψ : ι → ℝ) (m : ℝ) (s : E) : ℝ :=
  m / 2 * ‖s‖ ^ 2 + Finset.univ.sup' Finset.univ_nonempty
    (fun i ↦ ⟪s, z i - m • p i⟫ - ψ i + m / 2 * ‖p i‖ ^ 2)

/-- Algebraic equivalence of the affine and shifted-quadratic presentations. -/
theorem quadratic_piece_eq (z p s : E) (ψ m : ℝ) :
    m / 2 * ‖s‖ ^ 2 + (⟪s, z - m • p⟫ - ψ + m / 2 * ‖p‖ ^ 2) =
      ⟪s, z⟫ - ψ + m / 2 * ‖s-p‖ ^ 2 := by
  rw [inner_sub_right, inner_smul_right, norm_sub_sq_real]
  ring

theorem quadraticEnvelope_ge (z p : ι → E) (ψ : ι → ℝ) (m : ℝ) (s : E) (i : ι) :
    ⟪s, z i⟫ - ψ i + m / 2 * ‖s-p i‖ ^ 2 ≤ quadraticEnvelope z p ψ m s := by
  rw [← quadratic_piece_eq]
  have hb := Finset.le_sup'
    (fun j ↦ ⟪s, z j - m • p j⟫ - ψ j + m / 2 * ‖p j‖ ^ 2)
    (Finset.mem_univ i)
  dsimp [quadraticEnvelope]
  linarith

theorem quadraticEnvelope_le (z p : ι → E) (ψ : ι → ℝ) (m : ℝ) (s : E) (c : ℝ)
    (hc : ∀ i, ⟪s, z i⟫ - ψ i + m / 2 * ‖s-p i‖ ^ 2 ≤ c) :
    quadraticEnvelope z p ψ m s ≤ c := by
  dsimp [quadraticEnvelope]
  rw [add_comm, ← le_sub_iff_add_le]
  apply Finset.sup'_le
  intro i hi
  have hh := hc i
  rw [← quadratic_piece_eq] at hh
  linarith

theorem quadraticEnvelope_continuous (z p : ι → E) (ψ : ι → ℝ) (m : ℝ) :
    Continuous (quadraticEnvelope z p ψ m) := by
  apply Continuous.add
  · fun_prop
  · apply Continuous.finset_sup'_apply
    intro i hi
    fun_prop

theorem quadraticEnvelope_stronglyConvex (z p : ι → E) (ψ : ι → ℝ) (m : ℝ) :
    StrongConvexOn univ m (quadraticEnvelope z p ψ m) := by
  rw [strongConvexOn_iff_convex]
  convert convexOn_affine_max (fun i ↦ z i - m • p i)
    (fun i ↦ -ψ i + m / 2 * ‖p i‖ ^ 2) using 1
  ext s
  simp only [quadraticEnvelope, add_sub_cancel_left]
  congr 1
  ext i
  ring

/-- The usual finite smooth-convex interpolation inequality. -/
def InterpolationCondition (z p : ι → E) (ψ : ι → ℝ) (m : ℝ) : Prop :=
  ∀ i j, ψ i - ψ j - ⟪p j, z i-z j⟫ ≥ m / 2 * ‖p i-p j‖ ^ 2

/-- At a prescribed gradient, its own quadratic is an active envelope piece. -/
theorem quadraticEnvelope_at {z p : ι → E} {ψ : ι → ℝ} {m : ℝ}
    (h : InterpolationCondition z p ψ m) (i : ι) :
    quadraticEnvelope z p ψ m (p i) = ⟪p i, z i⟫ - ψ i := by
  apply le_antisymm
  · apply quadraticEnvelope_le
    intro j
    have hh := h j i
    rw [norm_sub_rev (p j)] at hh
    simp only [inner_sub_right] at hh
    linarith
  · simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero] using quadraticEnvelope_ge z p ψ m (p i) i

/-- Each active quadratic supplies the specified subgradient. -/
theorem quadraticEnvelope_subgradient {z p : ι → E} {ψ : ι → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (h : InterpolationCondition z p ψ m) (i : ι) (s : E) :
    quadraticEnvelope z p ψ m (p i) + ⟪z i, s-p i⟫ ≤ quadraticEnvelope z p ψ m s := by
  rw [quadraticEnvelope_at h i, inner_sub_right]
  have hi1 := real_inner_comm (z i) s
  have hi2 := real_inner_comm (z i) (p i)
  have hl := quadraticEnvelope_ge z p ψ m s i
  have hp : 0 ≤ m / 2 * ‖s-p i‖ ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
  linarith

/-- The origin datum makes the envelope a normalized positive quadratic core. -/
theorem quadraticEnvelope_core {z p : ι → E} {ψ : ι → ℝ} {m : ℝ}
    (hm : 0 < m) (h : InterpolationCondition z p ψ m)
    (o : ι) (hz : z o = 0) (hp : p o = 0) (hψ : ψ o = 0) :
    QuadraticCore (quadraticEnvelope z p ψ m) m where
  positive := hm
  continuous := quadraticEnvelope_continuous z p ψ m
  stronglyConvex := quadraticEnvelope_stronglyConvex z p ψ m
  zero := by simpa only [hp, hz, hψ, inner_zero_left, sub_self] using quadraticEnvelope_at h o
  lower := fun s ↦ by
    simpa only [hz, hp, hψ, inner_zero_right, sub_zero, zero_add] using
      quadraticEnvelope_ge z p ψ m s o

end SmoothInterpolation
