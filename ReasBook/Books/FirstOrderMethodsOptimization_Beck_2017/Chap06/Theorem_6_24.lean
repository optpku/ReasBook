/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

/- Theorem 6.24 is `bridge/view`: it identifies the proximal mapping of the indicator `δ_C` with
the source-facing set-valued projection map onto `C`. The owner abstractions already in the
project are Chapter 2's `extendedIndicator` and Chapter 6's `prox[f]`. Proposition 3.12's
single-valued `metricProjection` is intentionally not the core owner here, because Theorem 6.24
assumes only that `C` is nonempty and therefore works at the general minimizer-set level rather
than under closed-convex hypotheses. -/

/-- The set-valued projection mapping `P_C` sends `x` to the points of `C` minimizing
`y ↦ ‖y - x‖` over `C`. -/
def projection_mapping (C : Set E) : E → Set E :=
  fun x ↦ {y | y ∈ C ∧ IsMinOn (fun z ↦ ‖z - x‖) C y}

notation "P[" C "]" => projection_mapping C

-- Proof sketch: unfold `projection_mapping`; membership in `P[C] x` is definitionally the
-- conjunction that `y ∈ C` and that `y` minimizes the distance from `x` over `C`.
/-- A point `y` belongs to `P[C] x` exactly when `y ∈ C` and it minimizes the distance from `x`
over `C`. -/
@[simp]
theorem mem_projection_mapping_iff {C : Set E} {x y : E} :
    y ∈ P[C] x ↔ y ∈ C ∧ IsMinOn (fun z ↦ ‖z - x‖) C y :=
  Iff.rfl

/-- Every point in the projection set `P[C] x` belongs to `C`. -/
theorem mem_of_mem_projection_mapping {C : Set E} {x y : E} (hy : y ∈ P[C] x) :
    y ∈ C :=
  (mem_projection_mapping_iff.mp hy).1

/-- Any point in `P[C] x` realizes the infimum distance from `x` to `C`. -/
theorem norm_eq_iInf_of_mem_projection_mapping {C : Set E} {x y : E} (hy : y ∈ P[C] x) :
    ‖x - y‖ = ⨅ z : C, ‖x - z‖ := by
  have hyC : y ∈ C := mem_of_mem_projection_mapping hy
  have hyMin : IsMinOn (fun z ↦ ‖z - x‖) C y := (mem_projection_mapping_iff.mp hy).2
  simpa [norm_sub_rev] using (IsMinOn.iInf_eq hyC hyMin).symm

/-- If `x` has a projection onto `C` and every such projection point already lies in `D`, then
restricting `C` to `D ∩ C` does not change the projection set. -/
theorem projection_mapping_inter_eq_of_projection_mapping_subset
    (C D : Set E) (x : E)
    (hproj_nonempty : (P[C] x).Nonempty)
    (hproj_subset : P[C] x ⊆ D) :
    P[D ∩ C] x = P[C] x := by
  rcases hproj_nonempty with ⟨p, hp_proj_mem⟩
  have hpD : p ∈ D := hproj_subset hp_proj_mem
  rw [mem_projection_mapping_iff] at hp_proj_mem
  have hp_inter : p ∈ P[D ∩ C] x := by
    rw [mem_projection_mapping_iff]
    refine ⟨⟨hpD, hp_proj_mem.1⟩, ?_⟩
    simpa [Set.inter_comm] using hp_proj_mem.2.inter D
  ext y
  constructor
  · intro hy
    have hyC : y ∈ C := (mem_of_mem_projection_mapping hy).2
    have hy_eq : ‖x - y‖ = ‖x - p‖ := by
      rw [norm_eq_iInf_of_mem_projection_mapping hy]
      rw [norm_eq_iInf_of_mem_projection_mapping hp_inter]
    rw [mem_projection_mapping_iff, isMinOn_iff]
    refine ⟨hyC, ?_⟩
    intro z hz
    have hp_le : ‖p - x‖ ≤ ‖z - x‖ := by
      simpa [norm_sub_rev] using (isMinOn_iff.mp hp_proj_mem.2) z hz
    simpa [norm_sub_rev, hy_eq] using hp_le
  · intro hy
    rw [mem_projection_mapping_iff] at hy ⊢
    refine ⟨⟨hproj_subset ?_, hy.1⟩, ?_⟩
    · exact hy
    · rw [isMinOn_iff] at hy ⊢
      intro z hz
      exact hy.2 z hz.2

/-- In a proper normed additive group, every nonempty closed set has a nonempty projection set. -/
theorem projection_mapping_nonempty_of_nonempty_isClosed [ProperSpace E]
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (x : E) :
    (P[C] x).Nonempty := by
  obtain ⟨y, hyC, hyinf⟩ := hC_closed.exists_infDist_eq_dist hC_nonempty x
  refine ⟨y, ?_⟩
  rw [mem_projection_mapping_iff, isMinOn_iff]
  refine ⟨hyC, ?_⟩
  intro z hz
  have hz' : Metric.infDist x C ≤ dist x z := Metric.infDist_le_dist_of_mem hz
  simpa [dist_eq_norm, dist_comm, hyinf, norm_sub_rev] using hz'

section InnerProduct

variable [InnerProductSpace ℝ E]

-- Proof sketch: two points of `P[C] x` both realize the same infimum distance. The Hilbert-space
-- characterization `norm_eq_iInf_iff_real_inner_le_zero` turns each minimizing property into a
-- variational inequality. Evaluating these inequalities against the other point and combining them
-- forces the squared distance between the two points to be nonpositive, hence zero.
/-- For a convex set `C`, any two points in the projection set `P[C] x` coincide. -/
theorem eq_of_mem_projection_mapping {C : Set E} (hC_convex : Convex ℝ C) {x u v : E}
    (hu : u ∈ P[C] x) (hv : v ∈ P[C] x) : u = v := by
  have huC : u ∈ C := mem_of_mem_projection_mapping hu
  have hvC : v ∈ C := mem_of_mem_projection_mapping hv
  have hu_inner : ∀ w ∈ C, inner ℝ (x - u) (w - u) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hC_convex huC).1
      (norm_eq_iInf_of_mem_projection_mapping hu)
  have hv_inner : ∀ w ∈ C, inner ℝ (x - v) (w - v) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hC_convex hvC).1
      (norm_eq_iInf_of_mem_projection_mapping hv)
  have huv : inner ℝ (x - u) (v - u) ≤ 0 := hu_inner v hvC
  have hvu : inner ℝ (x - v) (u - v) ≤ 0 := hv_inner u huC
  have hnorm : ‖v - u‖ ^ (2 : ℕ) ≤ 0 := by
    calc
      ‖v - u‖ ^ (2 : ℕ) = inner ℝ (v - u) (v - u) := by
        rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ ((x - u) - (x - v)) (v - u) := by
        congr 1
        abel
      _ = inner ℝ (x - u) (v - u) - inner ℝ (x - v) (v - u) := by
        rw [inner_sub_left]
      _ ≤ 0 := by
        have hvu' : 0 ≤ inner ℝ (x - v) (v - u) := by
          have hvu'' : inner ℝ (x - v) (-(v - u)) ≤ 0 := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hvu
          rw [inner_neg_right] at hvu''
          linarith
        linarith
  have hzero : ‖v - u‖ = 0 := by
    nlinarith [sq_nonneg ‖v - u‖, hnorm]
  exact sub_eq_zero.mp <| norm_eq_zero.mp <| by
    simpa [norm_sub_rev] using hzero

/-- For a convex set `C`, the projection set `P[C] x` is a subsingleton. -/
theorem projection_mapping_subsingleton
    (C : Set E) (hC_convex : Convex ℝ C) (x : E) :
    (P[C] x).Subsingleton := by
  intro u hu v hv
  exact eq_of_mem_projection_mapping hC_convex hu hv

end InnerProduct

-- Proof sketch: unfold `prox[extendedIndicator C] x` and `extendedIndicator`. On `C`, the
-- proximal objective reduces to `(1 / 2) ‖y - x‖^2`, while outside `C` it is `⊤`, so its
-- minimizers are exactly the minimizers of `y ↦ ‖y - x‖^2` on `C`. Because `t ↦ t^2` is strictly
-- increasing on `[0, ∞)`, these are the same as the minimizers of `y ↦ ‖y - x‖` on `C`, namely
-- the points of `P[C] x`.
/-- Theorem 6.24: for a nonempty set `C`, the proximal mapping of the indicator function `δ_C`
coincides with the set-valued projection mapping `P_C`. -/
theorem prox_extendedIndicator_eq_projection_mapping (C : Set E) (hC : C.Nonempty) (x : E) :
    prox[extendedIndicator C] x = P[C] x := by
  ext y
  rw [mem_proximal_mapping_iff, mem_projection_mapping_iff, isMinOn_univ_iff]
  constructor
  · intro hy
    rcases hC with ⟨z, hz⟩
    have hyC : y ∈ C := by
      by_contra hyC
      have hyz : proximal_objective (extendedIndicator C) x y ≤
          proximal_objective (extendedIndicator C) x z := hy z
      have hytop : proximal_objective (extendedIndicator C) x y = ⊤ := by
        calc
          proximal_objective (extendedIndicator C) x y =
              (⊤ : EReal) + (((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
                simp [proximal_objective, extendedIndicator, hyC]
          _ = ⊤ := EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
      have hzcoe : proximal_objective (extendedIndicator C) x z =
          ((((1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
        simp [proximal_objective, extendedIndicator, hz]
      rw [hytop, hzcoe] at hyz
      have hnot : ¬ ((⊤ : EReal) ≤ ((((1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ)) : ℝ) : EReal)) := by
        simpa [top_le_iff] using
          (EReal.coe_ne_top (((1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ))))
      exact (hnot hyz).elim
    refine ⟨hyC, ?_⟩
    rw [isMinOn_iff]
    intro v hv
    have hyv :
        proximal_objective (extendedIndicator C) x y ≤
          proximal_objective (extendedIndicator C) x v :=
      hy v
    have hyv' : ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
        ((((1 / 2 : ℝ) * ‖v - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
      simpa [proximal_objective, extendedIndicator, hyC, hv] using hyv
    have hyv'' : (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * ‖v - x‖ ^ (2 : ℕ) := by
      exact_mod_cast hyv'
    have hsq : ‖y - x‖ ^ (2 : ℕ) ≤ ‖v - x‖ ^ (2 : ℕ) := by
      exact le_of_mul_le_mul_left hyv'' (by norm_num)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  · rintro ⟨hyC, hy⟩
    rw [isMinOn_iff] at hy
    intro v
    by_cases hv : v ∈ C
    · have hyv : ‖y - x‖ ≤ ‖v - x‖ := hy v hv
      have hsq : ‖y - x‖ ^ (2 : ℕ) ≤ ‖v - x‖ ^ (2 : ℕ) := by
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hyv
      have hscale : (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * ‖v - x‖ ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      have hscale' : ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
          ((((1 / 2 : ℝ) * ‖v - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
        exact_mod_cast hscale
      simpa [proximal_objective, extendedIndicator, hyC, hv] using hscale'
    · have hvtop : proximal_objective (extendedIndicator C) x v = ⊤ := by
        calc
          proximal_objective (extendedIndicator C) x v =
              (⊤ : EReal) + (((((1 / 2 : ℝ) * ‖v - x‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
                simp [proximal_objective, extendedIndicator, hv]
          _ = ⊤ := EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
      rw [hvtop]
      exact le_top

end
