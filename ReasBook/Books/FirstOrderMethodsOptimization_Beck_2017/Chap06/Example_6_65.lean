/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Metric
open AffineMap

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 6.65 is `source-facing`: the textbook item computes the proximal operator of the
half squared distance to a nonempty closed convex set. Domain sampling identifies the owner stack

- Proposition 3.12's complete-subset bridge `metricProjectionOfComplete`,
- the projection-ray identity proved below from the same variational inequality,
- Theorem 6.24's set-valued projection owner `P[C]`, and
- mathlib's canonical affine owner `AffineMap.lineMap`.

This separates primitive data from derived API correctly. The primitive data are only the set
`C`, its nonempty/complete/convex hypotheses, the base point `x`, and the scalar `λ ≥ 0`. The
ambient specialization "closed subset of a complete space" is only a downstream bridge via
`metricProjection`; the canonical owner data for the projection point are `IsComplete C` and
`Convex ℝ C`. The projection point is derived API, so the public theorem should reuse
`metricProjectionOfComplete` directly and express the affine combination through the owner
`lineMap` rather than through a bespoke local wrapper. -/

variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_complete : IsComplete C)
    (hC_convex : Convex ℝ C)

local notation "P" => metricProjectionOfComplete C hC_nonempty hC_complete hC_convex

/-- Helper for Example 6.65: points on the ray leaving `P x` in the direction of `x - P x`
keep the same metric projection onto `C`. -/
private lemma metricProjection_eq_along_projection_ray
    (x : E) (t : ℝ) (ht : 0 ≤ t) :
    P ((P x : E) + t • (x - P x)) = P x := by
  let y : E := (P x : E) + t • (x - P x)
  have hPx : (P x : E) ∈ C := (P x).2
  -- The projection inequality at `x` transfers to every point on the projection ray.
  have hy_Px : ∀ w ∈ C, inner ℝ (y - P x) (w - P x) ≤ 0 := by
    intro w hw
    have hx :=
      inner_sub_metricProjectionOfComplete_le_zero
        C hC_nonempty hC_complete hC_convex x w hw
    have hy : y - P x = t • (x - P x) := by
      dsimp [y]
      abel
    rw [hy, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos ht hx
  have hPx_min : ‖y - P x‖ = ⨅ z : C, ‖y - z‖ :=
    (norm_eq_iInf_iff_real_inner_le_zero hC_convex hPx).2 hy_Px
  have hPy_min : ‖y - P y‖ = ⨅ z : C, ‖y - z‖ := by
    simpa [y] using
      norm_sub_metricProjectionOfComplete_eq_iInf C hC_nonempty hC_complete hC_convex y
  have hPy : ∀ w ∈ C, inner ℝ (y - P y) (w - P y) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hC_convex (P y).2).1 hPy_min
  have h1 : inner ℝ (y - P y) (P x - P y) ≤ 0 := hPy (P x) hPx
  have h2 : inner ℝ (y - P x) (P y - P x) ≤ 0 := hy_Px (P y) (P y).2
  -- Comparing the two variational inequalities forces the projection points to coincide.
  have hnorm : ‖(P y : E) - P x‖ ^ 2 ≤ 0 := by
    calc
      ‖(P y : E) - P x‖ ^ 2 = inner ℝ ((P y : E) - P x) ((P y : E) - P x) := by
        rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ ((y - P x) - (y - P y)) ((P y : E) - P x) := by
        congr 1
        abel
      _ = inner ℝ (y - P x) ((P y : E) - P x) - inner ℝ (y - P y) ((P y : E) - P x) := by
        rw [inner_sub_left]
      _ ≤ 0 := by
        have h1' : 0 ≤ inner ℝ (y - P y) ((P y : E) - P x) := by
          have h1'' : inner ℝ (y - P y) (-(((P y : E) - P x))) ≤ 0 := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
          rw [inner_neg_right] at h1''
          linarith
        linarith
  have hzero : ‖(P y : E) - P x‖ = 0 := by
    nlinarith [sq_nonneg ‖(P y : E) - P x‖, hnorm]
  apply Subtype.ext
  exact sub_eq_zero.mp <| norm_eq_zero.mp hzero

/-- Helper for Example 6.65: the canonical metric projection belongs to the set-valued projection
mapping onto `C`. -/
lemma metricProjection_mem_projection_mapping (x : E) :
    (P x : E) ∈ P[C] x := by
  rw [mem_projection_mapping_iff, isMinOn_iff]
  constructor
  · exact (P x).2
  · intro z hz
    -- Compare the chosen projection distance with the ambient infimum over `C`.
    have h_bdd : BddBelow (Set.range fun w : C ↦ ‖x - w‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
    have h_inf_le : (⨅ w : C, ‖x - w‖) ≤ ‖x - z‖ := by
      simpa using ciInf_le h_bdd ⟨z, hz⟩
    have hproj : ‖x - P x‖ = ⨅ w : C, ‖x - w‖ :=
      norm_sub_metricProjectionOfComplete_eq_iInf C hC_nonempty hC_complete hC_convex x
    simpa [norm_sub_rev] using le_trans hproj.le h_inf_le

/-- Helper for Example 6.65: a point of `C` at the same distance from `x` as the metric
projection must coincide with the metric projection. -/
lemma metricProjection_eq_of_norm_eq_norm_sub_metricProjection
    (x c : E) (hc : c ∈ C) (hcmin : ‖x - c‖ = ‖x - P x‖) :
    c = (P x : E) := by
  have hp_proj : (P x : E) ∈ P[C] x :=
    metricProjection_mem_projection_mapping
      (C := C) (hC_nonempty := hC_nonempty) (hC_complete := hC_complete)
      (hC_convex := hC_convex) x
  have hc_proj : c ∈ P[C] x := by
    rw [mem_projection_mapping_iff, isMinOn_iff]
    constructor
    · exact hc
    · intro z hz
      have hp_min : IsMinOn (fun w ↦ ‖w - x‖) C (P x) :=
        (mem_projection_mapping_iff.mp hp_proj).2
      have hp_le : ‖(P x : E) - x‖ ≤ ‖z - x‖ := (isMinOn_iff.mp hp_min) z hz
      have hcmin' : ‖c - x‖ = ‖(P x : E) - x‖ := by
        simpa [norm_sub_rev] using hcmin
      calc
        ‖c - x‖ = ‖(P x : E) - x‖ := hcmin'
        _ ≤ ‖z - x‖ := hp_le
  -- Convex projection sets are subsingletons, so the two minimizing points agree.
  exact eq_of_mem_projection_mapping hC_convex hc_proj hp_proj

/-- Helper for Example 6.65: the quadratic objective with centers `x` and `c` completes the square
at the affine point `lineMap x c (λ / (λ + 1))`. -/
lemma two_point_quadratic_eq_completed_square
    (x c y : E) (lam : ℝ) (hlam : 0 ≤ lam) :
    (lam / 2) * ‖y - c‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) =
      ((lam + 1) / 2) * ‖y - lineMap x c (lam / (lam + 1))‖ ^ (2 : ℕ) +
        (lam / (2 * (lam + 1))) * ‖x - c‖ ^ (2 : ℕ) := by
  let z : E := lineMap x c (lam / (lam + 1))
  have hlam_one_pos : 0 < lam + 1 := add_pos_of_nonneg_of_pos hlam zero_lt_one
  have hyc := quadratic_translate_identity c z y
  have hyx := quadratic_translate_identity x z y
  have hyc' :
      (lam / 2) * ‖y - c‖ ^ (2 : ℕ) =
        (lam / 2) * ‖z - c‖ ^ (2 : ℕ) +
          lam * inner ℝ (z - c) (y - z) +
          (lam / 2) * ‖y - z‖ ^ (2 : ℕ) := by
    -- Multiply the translated quadratic identity by `λ`.
    have hyc0 := congrArg (fun t : ℝ ↦ lam * t) hyc
    nlinarith [hyc0]
  have hzc :
      z - c = ((1 : ℝ) / (lam + 1)) • (x - c) := by
    -- The affine center sits on the segment from `x` to `c` with residual weight `(λ + 1)⁻¹`.
    dsimp [z]
    rw [AffineMap.lineMap_apply_module']
    calc
      (lam / (lam + 1)) • (c - x) + x - c = ((lam / (lam + 1)) - 1) • (c - x) := by
        module
      _ = -((1 : ℝ) / (lam + 1)) • (c - x) := by
        have hcoeff : (lam / (lam + 1)) - 1 = -((1 : ℝ) / (lam + 1)) := by
          field_simp [hlam_one_pos.ne']
          ring_nf
        rw [hcoeff]
      _ = ((1 : ℝ) / (lam + 1)) • (x - c) := by
        module
  have hzx :
      z - x = (lam / (lam + 1)) • (c - x) := by
    -- The displacement from `x` to the affine center is the scaled direction from `x` to `c`.
    dsimp [z]
    rw [AffineMap.lineMap_apply_module']
    module
  have hcross :
      lam * inner ℝ (z - c) (y - z) + inner ℝ (z - x) (y - z) = 0 := by
    -- The mixed term vanishes because the chosen center balances the two quadratic weights.
    have hneg :
        (lam / (lam + 1)) • (c - x) = (-(lam / (lam + 1))) • (x - c) := by
      module
    rw [hzc, hzx, hneg, inner_smul_left, inner_smul_left]
    simp
    ring
  have hconst :
      (lam / 2) * ‖z - c‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) =
        (lam / (2 * (lam + 1))) * ‖x - c‖ ^ (2 : ℕ) := by
    -- The two endpoint terms collapse to the expected constant residual.
    rw [hzc, hzx, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_sub_rev]
    rw [abs_of_pos (one_div_pos.mpr hlam_one_pos), abs_of_nonneg (div_nonneg hlam hlam_one_pos.le)]
    field_simp [hlam_one_pos.ne']
    ring
  -- Insert the translated expansions and collect the surviving constant and square terms.
  calc
    (lam / 2) * ‖y - c‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)
        = ((lam / 2) * ‖z - c‖ ^ (2 : ℕ) +
            lam * inner ℝ (z - c) (y - z) +
            (lam / 2) * ‖y - z‖ ^ (2 : ℕ)) +
          ((1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) +
            inner ℝ (z - x) (y - z) +
            (1 / 2 : ℝ) * ‖y - z‖ ^ (2 : ℕ)) := by
              rw [hyc', hyx]
    _ = ((lam / 2) * ‖z - c‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ)) +
          ((lam / 2) * ‖y - z‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖y - z‖ ^ (2 : ℕ)) := by
            linarith
    _ = ((lam / 2) * ‖z - c‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ)) +
          (((lam + 1) / 2) * ‖y - z‖ ^ (2 : ℕ)) := by
            ring
    _ = ((lam + 1) / 2) * ‖y - z‖ ^ (2 : ℕ) +
          (lam / (2 * (lam + 1))) * ‖x - c‖ ^ (2 : ℕ) := by
            rw [hconst]
            ring
    _ = ((lam + 1) / 2) * ‖y - lineMap x c (lam / (lam + 1))‖ ^ (2 : ℕ) +
          (lam / (2 * (lam + 1))) * ‖x - c‖ ^ (2 : ℕ) := by
            simp [z]

-- Proof sketch: if `λ = 0`, the objective is the zero function, so the proximal set is `{x}`,
-- which is also `lineMap x (P x) 0`. If `λ > 0`, set `p = P x` and
-- `y⋆ = lineMap x p (λ / (λ + 1))`. Lemma 6.43 shows `P y⋆ = p`, so the completed-square
-- identity turns the proximal objective at an arbitrary `y` into a nonnegative square plus the
-- constant term `(λ / (2 (λ + 1))) ‖x - P y‖²`. Minimizing distance to `C` forces that constant
-- to be smallest at `p`, so `y⋆` is a proximal point. Equality in the same lower bound then
-- shows any proximal point must equal `lineMap x (P y) (λ / (λ + 1))` and have
-- `‖x - P y‖ = ‖x - p‖`, hence `P y = p` and finally `y = y⋆`.
/-- Example 6.65: if `C` is a nonempty complete convex subset of a real inner product space and
`λ ≥ 0`, then the proximal set of `y ↦ (λ / 2) d_C(y)^2` at `x` is the singleton containing
`lineMap x (P_C(x)) (λ / (λ + 1))`, equivalently `(λ / (λ + 1)) • P_C(x) + (1 / (λ + 1)) • x`,
where `P_C` denotes the canonical metric projection onto `C`. The textbook closed-subset-of-a-
complete-space formulation is the downstream specialization obtained from `IsClosed.isComplete`.
This is the chapter's set-valued rendering of
`prox_{(λ / 2) d_C^2}(x) = (λ / (λ + 1)) P_C(x) + (1 / (λ + 1)) x`. -/
theorem prox_half_sq_infDist_eq_singleton_metricProjection
    (lam : ℝ) (hlam : 0 ≤ lam) (x : E) :
    prox[fun y ↦ (((lam / 2) * infDist y C ^ 2 : ℝ) : EReal)] x =
      {lineMap x (P x) (lam / (lam + 1))} := by
  by_cases hlam_zero : lam = 0
  · -- At `λ = 0`, the objective is identically zero, so the proximal set is `{x}`.
    subst hlam_zero
    calc
      prox[fun y ↦ ((((0 : ℝ) / 2) * infDist y C ^ 2 : ℝ) : EReal)] x = prox[0] x := by
        refine congrArg (fun f : E → EReal ↦ prox[f] x) ?_
        ext y
        simp
      _ = {x} := prox_zero_eq_singleton x
      _ = {lineMap x (P x) ((0 : ℝ) / ((0 : ℝ) + 1))} := by
        simp
  · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (by simpa [eq_comm] using hlam_zero)
    have hlam_one_pos : 0 < lam + 1 := add_pos_of_nonneg_of_pos hlam zero_lt_one
    let p : E := P x
    let yStar : E := lineMap x p (lam / (lam + 1))
    let constTerm : ℝ := (lam / (2 * (lam + 1))) * ‖x - p‖ ^ (2 : ℕ)
    have hp_mem : p ∈ C := (P x).2
    have hyStar_ray :
        yStar = p + ((lam + 1)⁻¹ : ℝ) • (x - p) := by
      -- The textbook affine candidate lies on the projection ray from `p` through `x`.
      dsimp [yStar, p]
      rw [AffineMap.lineMap_apply_module']
      calc
        (lam / (lam + 1)) • ((P x : E) - x) + x =
            ((lam / (lam + 1)) - 1) • ((P x : E) - x) + (P x : E) := by
              module
        _ = -((1 : ℝ) / (lam + 1)) • ((P x : E) - x) + (P x : E) := by
            have hcoeff : (lam / (lam + 1)) - 1 = -((1 : ℝ) / (lam + 1)) := by
              field_simp [hlam_one_pos.ne']
              ring_nf
            rw [hcoeff]
        _ = (P x : E) + ((lam + 1)⁻¹ : ℝ) • (x - (P x : E)) := by
            module
    have hyStar_proj : (P yStar : E) = p := by
      -- Lemma 6.43 keeps the metric projection fixed along that ray.
      have hyStar_proj_subtype :
          P yStar = P x := by
        rw [hyStar_ray]
        exact metricProjection_eq_along_projection_ray
          (C := C) (hC_nonempty := hC_nonempty) (hC_complete := hC_complete)
          (hC_convex := hC_convex) x ((lam + 1)⁻¹)
          (by positivity)
      simpa [p] using congrArg Subtype.val hyStar_proj_subtype
    have hproj_le (c : E) (hc : c ∈ C) : ‖x - p‖ ≤ ‖x - c‖ := by
      -- The chosen metric projection realizes the minimum distance to `C`.
      have h_bdd : BddBelow (Set.range fun w : C ↦ ‖x - w‖) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨w, rfl⟩
        exact norm_nonneg _
      have h_inf_le : (⨅ w : C, ‖x - w‖) ≤ ‖x - c‖ := by
        simpa using ciInf_le h_bdd ⟨c, hc⟩
      have hproj :
          ‖x - p‖ = ⨅ w : C, ‖x - w‖ := by
        simpa [p] using
          norm_sub_metricProjectionOfComplete_eq_iInf C hC_nonempty hC_complete hC_convex x
      exact le_trans hproj.le h_inf_le
    have hobjective_eq (y : E) :
        (lam / 2) * infDist y C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) =
          ((lam + 1) / 2) * ‖y - lineMap x (P y) (lam / (lam + 1))‖ ^ (2 : ℕ) +
            (lam / (2 * (lam + 1))) * ‖x - P y‖ ^ (2 : ℕ) := by
      -- Rewrite the distance through the projection point and then complete the square.
      have hy_dist : infDist y C = ‖y - P y‖ := by
        calc
          infDist y C = dist y (P y) := by
            simpa using
              infDist_eq_dist_metricProjectionOfComplete C hC_nonempty hC_complete hC_convex y
          _ = ‖y - P y‖ := by rw [dist_eq_norm]
      rw [hy_dist]
      exact two_point_quadratic_eq_completed_square
        x (P y) y lam hlam
    have hyStar_obj :
        (lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ) =
          constTerm := by
      -- At the candidate point the completed-square defect vanishes.
      calc
        (lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ)
            = ((lam + 1) / 2) * ‖yStar - lineMap x (P yStar) (lam / (lam + 1))‖ ^ (2 : ℕ) +
                (lam / (2 * (lam + 1))) * ‖x - P yStar‖ ^ (2 : ℕ) := by
                  exact hobjective_eq yStar
        _ = ((lam + 1) / 2) * ‖yStar - lineMap x p (lam / (lam + 1))‖ ^ (2 : ℕ) +
              (lam / (2 * (lam + 1))) * ‖x - p‖ ^ (2 : ℕ) := by
                rw [hyStar_proj]
        _ = constTerm := by
          simp [constTerm, yStar]
    have hyStar_mem :
        yStar ∈ prox[fun y ↦ (((lam / 2) * infDist y C ^ 2 : ℝ) : EReal)] x := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
      intro y
      have hy_square_nonneg :
          0 ≤ ((lam + 1) / 2) * ‖y - lineMap x (P y) (lam / (lam + 1))‖ ^ (2 : ℕ) := by
        positivity
      have hy_proj_le : ‖x - p‖ ≤ ‖x - P y‖ := hproj_le (P y) (P y).2
      have hy_proj_sq :
          ‖x - p‖ ^ (2 : ℕ) ≤ ‖x - P y‖ ^ (2 : ℕ) := by
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy_proj_le
      have hy_const_le :
          constTerm ≤ (lam / (2 * (lam + 1))) * ‖x - P y‖ ^ (2 : ℕ) := by
        dsimp [constTerm]
        exact mul_le_mul_of_nonneg_left hy_proj_sq (by positivity)
      have hy_real :
          (lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ) ≤
            (lam / 2) * infDist y C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
        calc
          (lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ)
              = constTerm := hyStar_obj
          _ ≤ (lam / (2 * (lam + 1))) * ‖x - P y‖ ^ (2 : ℕ) := hy_const_le
          _ ≤ ((lam + 1) / 2) * ‖y - lineMap x (P y) (lam / (lam + 1))‖ ^ (2 : ℕ) +
                (lam / (2 * (lam + 1))) * ‖x - P y‖ ^ (2 : ℕ) := by
                  linarith
          _ = (lam / 2) * infDist y C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) :=
                (hobjective_eq y).symm
      have hy_ereal :
          ((((lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ) : ℝ)) :
              EReal) ≤
            ((((lam / 2) * infDist y C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ)) :
              EReal) := by
        exact_mod_cast hy_real
      simpa [proximal_objective_apply, yStar] using hy_ereal
    have hyStar_min :
        ∀ y : E,
          proximal_objective
              (fun y ↦ (((lam / 2) * infDist y C ^ 2 : ℝ) : EReal)) x yStar ≤
            proximal_objective
              (fun y ↦ (((lam / 2) * infDist y C ^ 2 : ℝ) : EReal)) x y := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hyStar_mem
      exact hyStar_mem
    refine Set.eq_singleton_iff_unique_mem.2 ?_
    constructor
    · simpa [yStar] using hyStar_mem
    · intro z hz
      have hz_min :
          ∀ y : E,
            proximal_objective
                (fun y ↦ (((lam / 2) * infDist y C ^ 2 : ℝ) : EReal)) x z ≤
              proximal_objective
                (fun y ↦ (((lam / 2) * infDist y C ^ 2 : ℝ) : EReal)) x y := by
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hz
        exact hz
      have hz_le_star_ereal :
          proximal_objective
              (fun y ↦ (((lam / 2) * infDist y C ^ 2 : ℝ) : EReal)) x z ≤
            proximal_objective
              (fun y ↦ (((lam / 2) * infDist y C ^ 2 : ℝ) : EReal)) x yStar :=
        hz_min yStar
      have hstar_le_z_ereal :
          proximal_objective
              (fun y ↦ (((lam / 2) * infDist y C ^ 2 : ℝ) : EReal)) x yStar ≤
            proximal_objective
              (fun y ↦ (((lam / 2) * infDist y C ^ 2 : ℝ) : EReal)) x z :=
        hyStar_min z
      have hz_le_star :
          (lam / 2) * infDist z C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) ≤ constTerm := by
        have hz_le_star_real :
            (((lam / 2) * infDist z C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) : ℝ) :
                EReal) ≤
              (((lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ) :
                  ℝ) : EReal) := by
          simpa [proximal_objective_apply] using hz_le_star_ereal
        have hz_le_star_real' :
            (lam / 2) * infDist z C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) ≤
              (lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ) := by
          exact_mod_cast hz_le_star_real
        calc
          (lam / 2) * infDist z C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ)
              ≤ (lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ) :=
                hz_le_star_real'
          _ = constTerm := hyStar_obj
      have hstar_le_z :
          constTerm ≤ (lam / 2) * infDist z C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
        have hstar_le_z_real :
            (((lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ) :
                ℝ) : EReal) ≤
              (((lam / 2) * infDist z C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) : ℝ) :
                EReal) := by
          simpa [proximal_objective_apply] using hstar_le_z_ereal
        have hstar_le_z_real' :
            (lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ) ≤
              (lam / 2) * infDist z C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
          exact_mod_cast hstar_le_z_real
        calc
          constTerm = (lam / 2) * infDist yStar C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖yStar - x‖ ^ (2 : ℕ) :=
            hyStar_obj.symm
          _ ≤ (lam / 2) * infDist z C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) :=
            hstar_le_z_real'
      have hz_obj_eq_const :
          (lam / 2) * infDist z C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) = constTerm :=
        le_antisymm hz_le_star hstar_le_z
      have hobjective_z := hobjective_eq z
      let squareTerm : ℝ :=
        ((lam + 1) / 2) * ‖z - lineMap x (P z) (lam / (lam + 1))‖ ^ (2 : ℕ)
      let projConst : ℝ :=
        (lam / (2 * (lam + 1))) * ‖x - P z‖ ^ (2 : ℕ)
      have hz_total_eq : squareTerm + projConst = constTerm := by
        calc
          squareTerm + projConst
              = (lam / 2) * infDist z C ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
                  simpa [squareTerm, projConst] using hobjective_z.symm
          _ = constTerm := hz_obj_eq_const
      have hz_square_nonneg : 0 ≤ squareTerm := by
        dsimp [squareTerm]
        positivity
      have hz_proj_le : ‖x - p‖ ≤ ‖x - P z‖ := hproj_le (P z) (P z).2
      have hz_proj_sq :
          ‖x - p‖ ^ (2 : ℕ) ≤ ‖x - P z‖ ^ (2 : ℕ) := by
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hz_proj_le
      have hz_const_ge : constTerm ≤ projConst := by
        dsimp [constTerm, projConst]
        exact mul_le_mul_of_nonneg_left hz_proj_sq (by positivity)
      have hz_const_le : projConst ≤ constTerm := by
        have : projConst ≤ squareTerm + projConst := by linarith
        exact this.trans_eq hz_total_eq
      have hz_const_eq : projConst = constTerm := le_antisymm hz_const_le hz_const_ge
      have hz_square_eq_zero : squareTerm = 0 := by
        linarith [hz_total_eq, hz_const_eq]
      have hz_line :
          z = lineMap x (P z) (lam / (lam + 1)) := by
        have hz_norm_sq_zero :
            ‖z - lineMap x (P z) (lam / (lam + 1))‖ ^ (2 : ℕ) = 0 := by
          have hcoeff_pos : 0 < (lam + 1) / 2 := by positivity
          dsimp [squareTerm] at hz_square_eq_zero
          nlinarith [hz_square_eq_zero]
        exact sub_eq_zero.mp
          (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hz_norm_sq_zero))
      have hz_proj_sq_eq :
          ‖x - P z‖ ^ (2 : ℕ) = ‖x - p‖ ^ (2 : ℕ) := by
        have hcoeff_pos : 0 < lam / (2 * (lam + 1)) := by positivity
        dsimp [projConst, constTerm] at hz_const_eq
        nlinarith [hz_const_eq]
      have hz_proj_norm : ‖x - P z‖ = ‖x - p‖ := by
        nlinarith [hz_proj_sq_eq, norm_nonneg (x - P z), norm_nonneg (x - p)]
      have hz_proj_eq : (P z : E) = p := by
        exact metricProjection_eq_of_norm_eq_norm_sub_metricProjection
          (C := C) (hC_nonempty := hC_nonempty) (hC_complete := hC_complete)
          (hC_convex := hC_convex) x (P z) (P z).2
          (by simpa [p] using hz_proj_norm)
      calc
        z = lineMap x (P z) (lam / (lam + 1)) := hz_line
        _ = lineMap x p (lam / (lam + 1)) := by rw [hz_proj_eq]
        _ = yStar := by rfl

end
