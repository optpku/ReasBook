/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A1.ClosedConvex
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

public section

noncomputable section

namespace EuclideanProjection

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section CompleteProjection

variable [CompleteSpace H]

/-- The Euclidean projection onto a nonempty closed convex set `C`, viewed as a map `H → H`. -/
def proj (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C) :
    H → H :=
  fun f ↦
    Classical.choose
      (exists_norm_eq_iInf_of_complete_convex hC_nonempty hC.isClosed.isComplete hC.convex f)

/- Source-facing notation for the metric projection operator onto `C`. -/
scoped notation "P_{" C " | " hC_nonempty ", " hC "}" => proj C hC_nonempty hC

open scoped EuclideanProjection

/-- Evaluating `proj C hC_nonempty hC` at `f` unfolds to the chosen minimizer
from `exists_norm_eq_iInf_of_complete_convex`. -/
theorem proj_apply (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C) (f : H) :
    (P_{C | hC_nonempty, hC}) f =
      Classical.choose
        (exists_norm_eq_iInf_of_complete_convex
          hC_nonempty
          hC.isClosed.isComplete
          hC.convex
          f) := by
  -- The owner is defined by this exact `Classical.choose`.
  rfl

/-- The Euclidean projection of `f` onto `C` lies in `C`. -/
theorem proj_mem (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C) (f : H) :
    (P_{C | hC_nonempty, hC}) f ∈ C := by
  -- Unpack the chosen witness and keep only its feasibility component.
  simpa [proj_apply C hC_nonempty hC f] using
    (Classical.choose_spec
      (exists_norm_eq_iInf_of_complete_convex
        hC_nonempty
        hC.isClosed.isComplete
        hC.convex
        f)).1

/-- The Euclidean projection of `f` onto `C` minimizes `v ↦ ‖f - v‖` on `C`. -/
theorem isMinOn_proj (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C) (f : H) :
    IsMinOn (fun v ↦ ‖f - v‖) C ((P_{C | hC_nonempty, hC}) f) := by
  -- Convert the infimum identity into the standard pointwise minimality statement.
  rw [isMinOn_iff]
  intro w hw
  calc
    ‖f - (P_{C | hC_nonempty, hC}) f‖ = ⨅ z : C, ‖f - z‖ := by
      simpa [proj_apply C hC_nonempty hC f] using
        (Classical.choose_spec
          (exists_norm_eq_iInf_of_complete_convex
            hC_nonempty
            hC.isClosed.isComplete
            hC.convex
            f)).2
    _ ≤ ‖f - ((⟨w, hw⟩ : C) : H)‖ := by
      apply ciInf_le
      use 0
      rintro y ⟨z, rfl⟩
      exact norm_nonneg _
    _ = ‖f - w‖ := by rfl

/-- The Euclidean projection specification bundles feasibility and closest-point minimality. -/
theorem proj_spec (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C) (f : H) :
    (P_{C | hC_nonempty, hC}) f ∈ C ∧
      IsMinOn (fun v ↦ ‖f - v‖) C ((P_{C | hC_nonempty, hC}) f) := by
  -- Bundle the feasibility and minimizer interfaces proved above.
  exact ⟨proj_mem C hC_nonempty hC f, isMinOn_proj C hC_nonempty hC f⟩

/-- The distance from `f` to its Euclidean projection onto `C` realizes the infimum over `C`. -/
theorem norm_eq_iInf_proj (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C)
    (f : H) :
    ‖f - (P_{C | hC_nonempty, hC}) f‖ =
      ⨅ w : C, ‖f - w‖ := by
  -- Keep the value component of the chosen minimizing witness.
  simpa [proj_apply C hC_nonempty hC f] using
    (Classical.choose_spec
      (exists_norm_eq_iInf_of_complete_convex
        hC_nonempty
        hC.isClosed.isComplete
        hC.convex
        f)).2

end CompleteProjection

/-- Helper for Definition 9.6: a feasible minimizer on a closed convex set satisfies the
projection variational inequality. -/
lemma innerLeZeroOfIsMinOn (C : Set H) (hC : Set.ClosedConvex C) (f y : H) (hy : y ∈ C)
    (hymin : IsMinOn (fun v ↦ ‖f - v‖) C y) :
    ∀ w ∈ C, inner ℝ (f - y) (w - y) ≤ 0 := by
  -- Repackage `IsMinOn` as the infimum identity expected by the mathlib characterization.
  have hyEq : ‖f - y‖ = ⨅ z : C, ‖f - z‖ := (IsMinOn.iInf_eq hy hymin).symm
  -- The convex-set minimizer characterization now applies directly.
  exact (norm_eq_iInf_iff_real_inner_le_zero hC.convex hy).1 hyEq

section CompleteProjection

variable [CompleteSpace H]

/-- The Euclidean projection satisfies the usual real-inner-product variational inequality. -/
theorem inner_le_zero_proj (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C)
    (f w : H) (hw : w ∈ C) :
    inner ℝ (f - (P_{C | hC_nonempty, hC}) f) (w - (P_{C | hC_nonempty, hC}) f) ≤ 0 := by
  -- Specialize the generic minimizer-to-variational-inequality bridge to the chosen projection.
  exact innerLeZeroOfIsMinOn
    C
    hC
    f
    ((P_{C | hC_nonempty, hC}) f)
    (proj_mem C hC_nonempty hC f)
    (isMinOn_proj C hC_nonempty hC f)
    w
    hw

/-- Any feasible minimizer of the distance-to-`f` function agrees with the chosen Euclidean
projection. -/
theorem eq_proj_of_mem_of_isMinOn (C : Set H) (hC_nonempty : C.Nonempty)
    (hC : Set.ClosedConvex C) (f y : H) (hy : y ∈ C)
    (hymin : IsMinOn (fun v ↦ ‖f - v‖) C y) :
    (P_{C | hC_nonempty, hC}) f = y := by
  let p := (P_{C | hC_nonempty, hC}) f
  let d := y - p
  have hp : p ∈ C := proj_mem C hC_nonempty hC f
  have hproj : inner ℝ (f - p) d ≤ 0 := by
    -- The projection inequality controls the direction from `p` to `y`.
    simpa [p, d] using inner_le_zero_proj C hC_nonempty hC f y hy
  have hyproj : inner ℝ (f - y) (p - y) ≤ 0 := innerLeZeroOfIsMinOn C hC f y hy hymin p hp
  have hyproj' : -inner ℝ (f - p) d + inner ℝ d d ≤ 0 := by
    -- Rewrite the minimizer inequality at `y` in terms of `d = y - p`.
    have hfy : f - y = f - p - d := by
      dsimp [d, p]
      abel
    have hpy : p - y = -d := by
      dsimp [d, p]
      abel
    rw [hfy, hpy, inner_neg_right, inner_sub_left] at hyproj
    simpa using hyproj
  have hnonneg : 0 ≤ inner ℝ d d := by
    -- A self-inner-product is a squared norm.
    simp
  have hle : inner ℝ d d ≤ 0 := by
    linarith
  have hdEq : d = 0 := by
    -- Vanishing squared norm forces the displacement to be zero.
    have hzeroInner : inner ℝ d d = 0 := le_antisymm hle hnonneg
    have hzeroNormSq : ‖d‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hzeroInner
    have hzeroNorm : ‖d‖ = 0 := by
      rw [pow_two] at hzeroNormSq
      exact mul_self_eq_zero.mp hzeroNormSq
    exact norm_eq_zero.mp hzeroNorm
  -- The zero displacement identifies the arbitrary minimizer with the projection.
  exact (sub_eq_zero.mp hdEq).symm

/-- For each `f`, there is a unique point of `C` minimizing the distance to `f`. -/
theorem existsUnique_proj (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C)
    (f : H) :
    ∃! y, y ∈ C ∧ IsMinOn (fun v ↦ ‖f - v‖) C y := by
  -- Use the chosen projection as the canonical witness.
  refine ⟨(P_{C | hC_nonempty, hC}) f, proj_spec C hC_nonempty hC f, ?_⟩
  intro y hy'
  -- Uniqueness follows from the minimizer-identification theorem.
  exact (eq_proj_of_mem_of_isMinOn C hC_nonempty hC f y hy'.1 hy'.2).symm

/-- Helper for Definition 9.6: the Euclidean projection map is nonexpansive on a closed convex
set. -/
lemma projDistLe (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C) (f g : H) :
    ‖(P_{C | hC_nonempty, hC}) f - (P_{C | hC_nonempty, hC}) g‖ ≤ ‖f - g‖ := by
  let p := (P_{C | hC_nonempty, hC}) f
  let q := (P_{C | hC_nonempty, hC}) g
  let d := p - q
  have hfp : 0 ≤ inner ℝ (f - p) d := by
    -- The projection inequality at `f` controls the sign of the first cross term.
    have h : inner ℝ (f - p) ((P_{C | hC_nonempty, hC}) g - p) ≤ 0 := by
      simpa [p, q] using
        inner_le_zero_proj C hC_nonempty hC f ((P_{C | hC_nonempty, hC}) g)
          (proj_mem C hC_nonempty hC g)
    have hqp : q - p = -d := by
      dsimp [d, q, p]
      abel
    have h' : -inner ℝ (f - p) d ≤ 0 := by
      rw [hqp, inner_neg_right] at h
      simpa using h
    linarith
  have hgq : inner ℝ (g - q) d ≤ 0 := by
    -- The projection inequality at `g` gives the second cross term directly.
    simpa [d, p, q] using
      inner_le_zero_proj C hC_nonempty hC g ((P_{C | hC_nonempty, hC}) f)
        (proj_mem C hC_nonempty hC f)
  have hcore : inner ℝ d d ≤ inner ℝ (f - g) d := by
    -- Expand `f - g` around the two projection points and use the sign information above.
    have hfg : f - g = (f - p) + d - (g - q) := by
      dsimp [d, p, q]
      abel
    have hexpand :
        inner ℝ (f - g) d = inner ℝ (f - p) d + inner ℝ d d - inner ℝ (g - q) d := by
      calc
        inner ℝ (f - g) d = inner ℝ ((f - p) + d - (g - q)) d := by rw [hfg]
        _ = inner ℝ ((f - p) + d) d - inner ℝ (g - q) d := by rw [inner_sub_left]
        _ = inner ℝ (f - p) d + inner ℝ d d - inner ℝ (g - q) d := by rw [inner_add_left]
    rw [hexpand]
    linarith
  have hmul : ‖d‖ * ‖d‖ ≤ ‖f - g‖ * ‖d‖ := by
    -- Compare the self-inner-product of `d` to the Cauchy-Schwarz bound.
    calc
      ‖d‖ * ‖d‖ = inner ℝ d d := by
        rw [real_inner_self_eq_norm_mul_norm]
      _ ≤ inner ℝ (f - g) d := hcore
      _ ≤ ‖f - g‖ * ‖d‖ := real_inner_le_norm _ _
  by_cases hd : ‖d‖ = 0
  · -- The degenerate case collapses immediately.
    have hzero : ‖d‖ ≤ ‖f - g‖ := by
      simp [hd]
    simpa [d] using hzero
  · -- Otherwise cancel the positive factor `‖d‖`.
    have hdPos : 0 < ‖d‖ := by
      refine lt_of_le_of_ne (norm_nonneg _) ?_
      exact fun h0 => hd h0.symm
    have : ‖d‖ ≤ ‖f - g‖ := le_of_mul_le_mul_right hmul hdPos
    simpa [d] using this

/-- The Euclidean projection map onto a nonempty closed convex set is continuous. -/
theorem continuous_proj (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C) :
    Continuous (P_{C | hC_nonempty, hC}) := by
  -- The nonexpansive estimate upgrades immediately to Lipschitz continuity.
  refine (LipschitzWith.mk_one ?_).continuous
  intro f g
  simpa [dist_eq_norm] using projDistLe C hC_nonempty hC f g

/-- A feasible point is fixed by its Euclidean projection. -/
theorem proj_eq_self_of_mem (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C)
    {f : H} (hf : f ∈ C) :
    (P_{C | hC_nonempty, hC}) f = f := by
  have hfmin : IsMinOn (fun v ↦ ‖f - v‖) C f := by
    -- The feasible point `f` attains the obvious lower bound `0`.
    rw [isMinOn_iff]
    intro w hw
    simp
  -- The uniqueness statement identifies the projection with this feasible minimizer.
  exact eq_proj_of_mem_of_isMinOn C hC_nonempty hC f f hf hfmin

end CompleteProjection

end EuclideanProjection
