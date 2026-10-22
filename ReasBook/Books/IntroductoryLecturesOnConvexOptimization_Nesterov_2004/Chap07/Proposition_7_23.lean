/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {X : Type u}

open scoped Pointwise

/-- Helper for Proposition 7.23: if the feasible objective values are nonempty and bounded below,
then the Chapter 1 owner optimal value agrees with the textbook real infimum, viewed in `EReal`.
-/
private theorem optimalValue_eq_coe_sInf_of_nonempty_bddBelow
    (Q : Set X) (g : X → ℝ) (hQ : Q.Nonempty) (hbounded : BddBelow (g '' Q)) :
    (.mk Q g : SetConstrainedMinimizationProblem X).optimalValue =
      ((sInf (g '' Q) : ℝ) : EReal) := by
  -- Transport the real greatest-lower-bound characterization across the coercion `ℝ → EReal`.
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  have hs :
      IsGLB ((fun x : ℝ ↦ (x : EReal)) '' (g '' Q)) (((sInf (g '' Q) : ℝ) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact EReal.coe_le_coe (csInf_le hbounded hy)
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          intro hz_eq_top
          rcases hQ with ⟨x, hx⟩
          have hz_mem : z ≤ (g x : EReal) := hz ⟨g x, ⟨x, hx, rfl⟩, rfl⟩
          simp [hz_eq_top] at hz_mem
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : r ≤ sInf (g '' Q) := by
          refine le_csInf (hQ.image g) ?_
          intro y hy
          have hzy : (r : EReal) ≤ (y : EReal) := hz ⟨y, hy, rfl⟩
          exact_mod_cast hzy
        exact_mod_cast hr
  have hs' : ((fun x : ℝ ↦ (x : EReal)) '' (g '' Q)).Nonempty := by
    rcases hQ with ⟨x, hx⟩
    exact ⟨g x, ⟨g x, ⟨x, hx, rfl⟩, rfl⟩⟩
  simpa [Set.image_image] using hs.csInf_eq hs'

/-- Helper for Proposition 7.23: under nonemptiness and a real lower bound on the feasible image,
the owner optimal value projects back to the textbook real infimum via `.toReal`. -/
private theorem optimalValue_toReal_eq_sInf_of_nonempty_bddBelow
    (Q : Set X) (g : X → ℝ) (hQ : Q.Nonempty) (hbounded : BddBelow (g '' Q)) :
    ((.mk Q g : SetConstrainedMinimizationProblem X).optimalValue).toReal = sInf (g '' Q) := by
  -- First identify the owner value with a finite `EReal`, then remove the coercion.
  rw [optimalValue_eq_coe_sInf_of_nonempty_bddBelow Q g hQ hbounded]
  simp

/-- Helper for Proposition 7.23: on a nonnegative feasible image, squaring commutes with taking
the infimum. -/
private theorem sInf_sq_image_eq_sq_sInf_image_of_nonneg
    (Q : Set X) (φ : X → ℝ) (hQ : Q.Nonempty) (hφ_nonneg : ∀ y ∈ Q, 0 ≤ φ y) :
    sInf ((fun y ↦ φ y ^ (2 : ℕ)) '' Q) = (sInf (φ '' Q)) ^ (2 : ℕ) := by
  let A : Set ℝ := φ '' Q
  have hA_nonempty : A.Nonempty := by
    simpa [A] using hQ.image φ
  have hA_bddBelow : BddBelow A := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hφ_nonneg y hy
  have hA_subset : A ⊆ Set.Ici 0 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hφ_nonneg y hy
  have hmono : MonotoneOn (fun x : ℝ ↦ x * x) A := by
    exact (strictMonoOn_mul_self.monotoneOn).mono hA_subset
  have hsq :
      (sInf A) * sInf A = sInf ((fun x : ℝ ↦ x * x) '' A) := by
    -- The square map is continuous and monotone on the nonnegative feasible image.
    simpa [pow_two] using
      (MonotoneOn.map_csInf_of_continuousWithinAt
        (A := A) (f := fun x : ℝ ↦ x * x)
        (continuous_id.mul continuous_id).continuousWithinAt
        hmono hA_nonempty hA_bddBelow)
  have himage :
      ((fun x : ℝ ↦ x * x) '' A) = ((fun y ↦ φ y ^ (2 : ℕ)) '' Q) := by
    ext z
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp [pow_two]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨φ y, ⟨y, hy, rfl⟩, by simp [pow_two]⟩
  -- Rewrite the image back from the intermediate feasible-value set `A`.
  simpa [A, himage, pow_two] using hsq.symm

/-- Helper for Proposition 7.23: the pointwise upper sandwich transfers to the owner optimal value
of `f_p`, with the `r^(1/p)` factor dominated by `exp(log r / p)`. -/
private theorem fp_optimalValue_toReal_le_exp_log_div_mul_phi_optimalValue_sq
    (Q : Set X) (φ f_p : X → ℝ) (r : ℝ) (p : ℕ+) (yBar : X)
    (hyBar_mem : yBar ∈ Q)
    (hφ_nonneg : ∀ y ∈ Q, 0 ≤ φ y)
    (h_lower : ∀ y ∈ Q, (1 / 2 : ℝ) * φ y ^ (2 : ℕ) ≤ f_p y)
    (h_upper : ∀ y ∈ Q,
      f_p y ≤ (1 / 2 : ℝ) * Real.rpow r (1 / (p : ℝ)) * φ y ^ (2 : ℕ)) :
    ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal ≤
      (1 / 2 : ℝ) * Real.exp (Real.log r / (p : ℝ)) *
        (((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal) ^ (2 : ℕ) := by
  let c : ℝ := (1 / 2 : ℝ) * Real.exp (Real.log r / (p : ℝ))
  have hQ : Q.Nonempty := ⟨yBar, hyBar_mem⟩
  have hφ_bddBelow : BddBelow (φ '' Q) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hφ_nonneg y hy
  have hfp_bddBelow : BddBelow (f_p '' Q) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) * φ y ^ (2 : ℕ) := by positivity
    exact hhalf_nonneg.trans (h_lower y hy)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hpointwise :
      ∀ y ∈ Q, f_p y ≤ c * φ y ^ (2 : ℕ) := by
    intro y hy
    have hrpow_le :
        Real.rpow r (1 / (p : ℝ)) ≤ Real.exp (Real.log r / (p : ℝ)) := by
      calc
        Real.rpow r (1 / (p : ℝ))
            ≤ |Real.rpow r (1 / (p : ℝ))| := le_abs_self _
        _ ≤ Real.exp (Real.log r * (1 / (p : ℝ))) :=
          Real.abs_rpow_le_exp_log_mul r (1 / (p : ℝ))
        _ = Real.exp (Real.log r / (p : ℝ)) := by
          congr 1
          rw [div_eq_mul_inv]
          ring
    have hcoeff :
        (1 / 2 : ℝ) * Real.rpow r (1 / (p : ℝ)) ≤
          (1 / 2 : ℝ) * Real.exp (Real.log r / (p : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hrpow_le (by positivity)
    have hmul :
        ((1 / 2 : ℝ) * Real.rpow r (1 / (p : ℝ))) * φ y ^ (2 : ℕ) ≤
          ((1 / 2 : ℝ) * Real.exp (Real.log r / (p : ℝ))) * φ y ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
    calc
      f_p y ≤ (1 / 2 : ℝ) * Real.rpow r (1 / (p : ℝ)) * φ y ^ (2 : ℕ) := h_upper y hy
      _ ≤ ((1 / 2 : ℝ) * Real.exp (Real.log r / (p : ℝ))) * φ y ^ (2 : ℕ) := hmul
      _ = c * φ y ^ (2 : ℕ) := rfl
  have hsInf_le :
      sInf (f_p '' Q) ≤ sInf ((fun y ↦ c * φ y ^ (2 : ℕ)) '' Q) := by
    refine le_csInf (hQ.image fun y ↦ c * φ y ^ (2 : ℕ)) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (csInf_le hfp_bddBelow ⟨y, hy, rfl⟩).trans (hpointwise y hy)
  have hsInf_target :
      sInf ((fun y ↦ c * φ y ^ (2 : ℕ)) '' Q) =
        c * (sInf (φ '' Q)) ^ (2 : ℕ) := by
    have himage :
        ((fun y ↦ c * φ y ^ (2 : ℕ)) '' Q) = c • ((fun y ↦ φ y ^ (2 : ℕ)) '' Q) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨φ y ^ (2 : ℕ), ⟨y, hy, rfl⟩, by simp [smul_eq_mul, mul_comm]⟩
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, by simp [smul_eq_mul, mul_comm]⟩
    calc
      sInf ((fun y ↦ c * φ y ^ (2 : ℕ)) '' Q)
          = sInf (c • ((fun y ↦ φ y ^ (2 : ℕ)) '' Q)) := by rw [himage]
      _ = c • sInf ((fun y ↦ φ y ^ (2 : ℕ)) '' Q) := by
        simpa using Real.sInf_smul_of_nonneg hc_nonneg ((fun y ↦ φ y ^ (2 : ℕ)) '' Q)
      _ = c * sInf ((fun y ↦ φ y ^ (2 : ℕ)) '' Q) := by simp [smul_eq_mul]
      _ = c * (sInf (φ '' Q)) ^ (2 : ℕ) := by
        rw [sInf_sq_image_eq_sq_sInf_image_of_nonneg Q φ hQ hφ_nonneg]
  have hfp_toReal :
      ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal = sInf (f_p '' Q) :=
    optimalValue_toReal_eq_sInf_of_nonempty_bddBelow Q f_p hQ hfp_bddBelow
  have hφ_toReal :
      ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal = sInf (φ '' Q) :=
    optimalValue_toReal_eq_sInf_of_nonempty_bddBelow Q φ hQ hφ_bddBelow
  -- Rewrite both owner values to real infima and compare them through the pointwise sandwich.
  calc
    ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal = sInf (f_p '' Q) :=
      hfp_toReal
    _ ≤ c * (sInf (φ '' Q)) ^ (2 : ℕ) := by
      simpa [hsInf_target] using hsInf_le
    _ = (1 / 2 : ℝ) * Real.exp (Real.log r / (p : ℝ)) *
          (((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal) ^ (2 : ℕ) := by
      rw [hφ_toReal]

/-- Helper for Proposition 7.23: the parameter condition on `p` implies the exponential smoothing
factor is bounded by `1 + δ`. -/
private theorem exp_log_div_le_one_add_delta
    (δ r : ℝ) (p : ℕ+) (hδ : 0 < δ)
    (hp : ((1 + δ) / δ) * Real.log r ≤ (p : ℝ)) :
    Real.exp (Real.log r / (p : ℝ)) ≤ 1 + δ := by
  have hδ1 : 0 < 1 + δ := by linarith
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast p.pos
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ
  have hδ1_ne : 1 + δ ≠ 0 := ne_of_gt hδ1
  have hlog_le_mul : Real.log r ≤ (p : ℝ) * (δ / (1 + δ)) := by
    have hscaled :
        (δ / (1 + δ)) * (((1 + δ) / δ) * Real.log r) ≤ (δ / (1 + δ)) * (p : ℝ) := by
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    have hcancel : (δ / (1 + δ)) * ((1 + δ) / δ) = (1 : ℝ) := by
      field_simp [hδ_ne, hδ1_ne]
    calc
      Real.log r = ((δ / (1 + δ)) * ((1 + δ) / δ)) * Real.log r := by rw [hcancel, one_mul]
      _ = (δ / (1 + δ)) * (((1 + δ) / δ) * Real.log r) := by ring
      _ ≤ (δ / (1 + δ)) * (p : ℝ) := hscaled
      _ = (p : ℝ) * (δ / (1 + δ)) := by ring
  have hlog_div : Real.log r / (p : ℝ) ≤ δ / (1 + δ) := by
    refine (div_le_iff₀ hp_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlog_le_mul
  have hfrac_le_log : δ / (1 + δ) ≤ Real.log (1 + δ) := by
    have hlog := Real.one_sub_inv_le_log_of_pos hδ1
    have hfrac :
        1 - (1 + δ)⁻¹ = δ / (1 + δ) := by
      field_simp [hδ1_ne]
      ring
    simpa [hfrac] using hlog
  -- Move to logarithms and then return through monotonicity of `exp`.
  exact (Real.le_log_iff_exp_le hδ1).1 (hlog_div.trans hfrac_le_log)

/- Proposition 7.23 lies in Chapter 7's relative-accuracy / constrained-optimal-value transfer
domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  real-valued objective on a feasible set;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  constrained optimal-value owner;
- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Chap01/Definition_1_3_7`,
  the defining bridge to the infimum of the feasible value image in `EReal`;
- `inducedObjectiveInf` and `inducedRadiusInf` in `Chap07/Proposition_7_22`, the nearby chapter
  pattern using the same owner together with a `.toReal` bridge back to textbook real inequalities.

Best owner abstraction:
- source-facing: transfer of a relative-accuracy bound from the smoothed objective `f_p` to the
  original objective `φ` on the same feasible set;
- core/canonical: `(.mk Q f : SetConstrainedMinimizationProblem X).optimalValue`;
- bridge/view: the pointwise sandwich between `φ` and `f_p`.

Primitive data:
- a feasible set `Q : Set X`;
- the two objectives `φ` and `f_p`;
- a positive smoothing order `p : ℕ+`;
- the candidate point `yBar ∈ Q`;
- the feasible-set nonnegativity of `φ`;
- the pointwise lower and upper comparisons between `φ` and `f_p` on `Q`.

Derived API:
- the constrained optimization owners `(.mk Q φ : SetConstrainedMinimizationProblem X)` and
  `(.mk Q f_p : SetConstrainedMinimizationProblem X)`;
- the textbook real surfaces `((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal`
  and `((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal`;
- the relative-accuracy inequalities stated using those owners.

This refinement removes the duplicate local real-valued optimal-value wheel from the public
surface. The constrained minima of `φ` and `f_p` are canonically owned by
`SetConstrainedMinimizationProblem.optimalValue`; the proposition uses only the minimal `.toReal`
bridge needed to recover the textbook real inequalities from those owner values.
-/

-- Proof sketch: combine the feasible-set nonnegativity of `φ` with the pointwise bounds to get
-- `φ yBar ≤ sqrt (2 * f_p yBar)` and
-- `sqrt (2 * ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal) ≤
--   r^(1 / (2p)) * ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal`,
-- then use
-- `f_p yBar ≤ (1 + δ) *
--   ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal`.
-- The condition
-- `((1 + δ) / δ) * log r ≤ p` implies `r^(1 / (2p)) ≤ sqrt (1 + δ)` when `r > 1`; for `r ≤ 1`,
-- the factor `r^(1 / (2p))` only decreases the right-hand side, so the same conclusion is easier.
-- Thus
-- `φ yBar / ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal ≤
--   r^(1 / (2p)) * sqrt (1 + δ) ≤ 1 + δ`.
/-- Proposition 7.23: if `p` is a positive smoothing order, `f_p` lies between
`(1 / 2) φ^2` and `(1 / 2) r^(1 / p) φ^2` on the feasible set `Q`, and `yBar ∈ Q` is
`(1 + δ)`-optimal for `f_p`, then `yBar` is also `(1 + δ)`-optimal for `φ`, with both optimal
values read from the canonical Chapter 1 constrained optimization owner and projected back to `ℝ`
via `.toReal`. -/
theorem relative_accuracy_transfer_from_fp_to_phi
    (Q : Set X) (φ f_p : X → ℝ) (δ r : ℝ) (p : ℕ+) (yBar : X)
    (hyBar_mem : yBar ∈ Q)
    (hδ : 0 < δ)
    (hφ_nonneg : ∀ y ∈ Q, 0 ≤ φ y)
    (h_lower : ∀ y ∈ Q, (1 / 2 : ℝ) * φ y ^ (2 : ℕ) ≤ f_p y)
    (h_upper : ∀ y ∈ Q,
      f_p y ≤ (1 / 2 : ℝ) * Real.rpow r (1 / (p : ℝ)) * φ y ^ (2 : ℕ))
    (hp : ((1 + δ) / δ) * Real.log r ≤ (p : ℝ))
    (hyBar :
      f_p yBar ≤
        (1 + δ) * ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal) :
    φ yBar ≤
      (1 + δ) * ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal := by
  let φStar : ℝ := ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal
  let fpStar : ℝ := ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal
  have hQ : Q.Nonempty := ⟨yBar, hyBar_mem⟩
  have hφ_bddBelow : BddBelow (φ '' Q) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hφ_nonneg y hy
  have hφStar_eq : φStar = sInf (φ '' Q) := by
    dsimp [φStar]
    exact optimalValue_toReal_eq_sInf_of_nonempty_bddBelow Q φ hQ hφ_bddBelow
  have hφStar_nonneg : 0 ≤ φStar := by
    rw [hφStar_eq]
    refine le_csInf (hQ.image φ) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hφ_nonneg y hy
  have hfp_bound :
      fpStar ≤ (1 / 2 : ℝ) * Real.exp (Real.log r / (p : ℝ)) * φStar ^ (2 : ℕ) := by
    dsimp [fpStar, φStar]
    exact fp_optimalValue_toReal_le_exp_log_div_mul_phi_optimalValue_sq
      Q φ f_p r p yBar hyBar_mem hφ_nonneg h_lower h_upper
  have hexp_le : Real.exp (Real.log r / (p : ℝ)) ≤ 1 + δ :=
    exp_log_div_le_one_add_delta δ r p hδ hp
  have hδ_nonneg : 0 ≤ 1 + δ := by linarith
  have hyBar_sq :
      φ yBar ^ (2 : ℕ) ≤ ((1 + δ) * φStar) ^ (2 : ℕ) := by
    have hfp_bound' :
        fpStar ≤ (1 / 2 : ℝ) * (1 + δ) * φStar ^ (2 : ℕ) := by
      have hscaled :
          (1 / 2 : ℝ) * Real.exp (Real.log r / (p : ℝ)) ≤ (1 / 2 : ℝ) * (1 + δ) := by
        exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
      calc
        fpStar ≤ (1 / 2 : ℝ) * Real.exp (Real.log r / (p : ℝ)) * φStar ^ (2 : ℕ) := hfp_bound
        _ ≤ ((1 / 2 : ℝ) * (1 + δ)) * φStar ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_right hscaled (by positivity)
        _ = (1 / 2 : ℝ) * (1 + δ) * φStar ^ (2 : ℕ) := by ring
    have hyBar_fp :
        f_p yBar ≤ (1 / 2 : ℝ) * (1 + δ) ^ (2 : ℕ) * φStar ^ (2 : ℕ) := by
      have hscaled :
          (1 + δ) * fpStar ≤ (1 + δ) * ((1 / 2 : ℝ) * (1 + δ) * φStar ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hfp_bound' hδ_nonneg
      calc
        f_p yBar ≤ (1 + δ) * fpStar := by simpa [fpStar] using hyBar
        _ ≤ (1 + δ) * ((1 / 2 : ℝ) * (1 + δ) * φStar ^ (2 : ℕ)) := hscaled
        _ = (1 / 2 : ℝ) * (1 + δ) ^ (2 : ℕ) * φStar ^ (2 : ℕ) := by ring
    have hhalf_sq :
        (1 / 2 : ℝ) * φ yBar ^ (2 : ℕ) ≤
          (1 / 2 : ℝ) * (((1 + δ) * φStar) ^ (2 : ℕ)) := by
      calc
        (1 / 2 : ℝ) * φ yBar ^ (2 : ℕ) ≤ f_p yBar := h_lower yBar hyBar_mem
        _ ≤ (1 / 2 : ℝ) * (1 + δ) ^ (2 : ℕ) * φStar ^ (2 : ℕ) := hyBar_fp
        _ = (1 / 2 : ℝ) * (((1 + δ) * φStar) ^ (2 : ℕ)) := by ring
    -- Clear the common factor `1 / 2` before applying the square-root monotonicity step.
    nlinarith
  have hφyBar_nonneg : 0 ≤ φ yBar := hφ_nonneg yBar hyBar_mem
  -- Finish by comparing squares on the nonnegative side.
  exact (sq_le_sq₀ hφyBar_nonneg (mul_nonneg hδ_nonneg hφStar_nonneg)).1 hyBar_sq

end
