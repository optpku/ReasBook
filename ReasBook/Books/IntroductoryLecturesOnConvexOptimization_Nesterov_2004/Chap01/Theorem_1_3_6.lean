/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open SetConstrainedMinimizationProblem

/- The only source-facing primitive data in this item are the midpoint grid points, expressed
pointwise on `EuclideanSpace ℝ (Fin n)`. The midpoint grid itself is the derived range of those
points. The surrounding optimization notions are reused from their chapter owners:
`zeroOneBox`, `𝒫∞[n, L]`, and `SetConstrainedMinimizationProblem.IsApproximateMinimizer`. The
auxiliary theorems below are bridge lemmas from `uniformGridPoint` and `uniformGrid` to those
owner abstractions. -/

/-- The midpoint grid point of mesh `1 / p` indexed by `α ∈ {0, ..., p - 1}^n`. -/
def uniformGridPoint (n : ℕ) (p : ℕ+) (α : Fin n → Fin p) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ (((α i : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ))

/-- The uniform midpoint grid of mesh `1 / p` inside `[0,1]^n`. -/
def uniformGrid (n : ℕ) (p : ℕ+) : Set (EuclideanSpace ℝ (Fin n)) :=
  Set.range (uniformGridPoint n p)

@[simp] theorem uniformGridPoint_apply
    (n : ℕ) (p : ℕ+) (α : Fin n → Fin p) (i : Fin n) :
    uniformGridPoint n p α i = (((α i : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ) :=
  by simp [uniformGridPoint]

/-- Each midpoint grid point lies in the cube `[0,1]^n`. -/
theorem uniformGridPoint_mem_zeroOneBox (p : ℕ+) (α : Fin n → Fin p) :
    uniformGridPoint n p α ∈ zeroOneBox n := by
  rw [mem_zeroOneBox_iff]
  intro i
  refine ⟨by simpa [uniformGridPoint] using
      (show 0 ≤ (((α i : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ) by positivity), ?_⟩
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.pos
  have hα : ((α i : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (α i).is_lt
  rw [uniformGridPoint_apply n, div_le_iff₀ hp]
  nlinarith

/-- The midpoint grid is contained in the cube `[0,1]^n`. -/
theorem uniformGrid_subset_zeroOneBox (p : ℕ+) :
    uniformGrid n p ⊆ zeroOneBox n := by
  rintro _ ⟨α, rfl⟩
  exact uniformGridPoint_mem_zeroOneBox p α

/-- Helper for Theorem 1.3.6: every scalar coordinate in `[0,1]` is within `1 / (2p)` of some
midpoint of the uniform partition of `[0,1]` into `p` subintervals. -/
theorem exists_midpoint_coordinate_close (p : ℕ+) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin p, |t - ((((i : Fin p) : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ)| ≤
      1 / (2 * (p : ℝ)) := by
  rcases ht with ⟨ht0, ht1⟩
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.pos
  by_cases htop : t = 1
  · -- The endpoint `t = 1` is covered by the last midpoint.
    have hpred_lt : ((p : ℕ) - 1) < p := by
      exact Nat.sub_lt (Nat.succ_le_of_lt p.pos) (by decide)
    refine ⟨⟨((p : ℕ) - 1), hpred_lt⟩, ?_⟩
    have hpred : (((p : ℕ) - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
      norm_num [Nat.succ_pred_eq_of_pos p.pos]
    rw [htop, abs_le]
    constructor
    · field_simp [hp.ne']
      nlinarith [hpred]
    · field_simp [hp.ne']
      nlinarith [hpred]
  · -- Away from the endpoint, the floor of `p * t` selects the containing subinterval.
    let m : ℕ := Nat.floor ((p : ℝ) * t)
    have hscaled_nonneg : 0 ≤ (p : ℝ) * t := by
      positivity
    have hm_lt_p : m < p := by
      have ht_lt_one : t < 1 := lt_of_le_of_ne ht1 htop
      have hscaled_lt : (p : ℝ) * t < p := by
        nlinarith
      exact (Nat.floor_lt hscaled_nonneg).2 hscaled_lt
    refine ⟨⟨m, hm_lt_p⟩, ?_⟩
    have hm_le : (m : ℝ) ≤ (p : ℝ) * t := by
      exact Nat.floor_le hscaled_nonneg
    have hm_succ : (p : ℝ) * t < (m : ℝ) + 1 := by
      simpa [m] using (Nat.lt_floor_add_one ((p : ℝ) * t))
    have hlower :
        ((((m : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ)) - (1 / (2 * (p : ℝ))) ≤ t := by
      field_simp [hp.ne']
      nlinarith
    have hupper :
        t ≤ ((((m : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ)) + (1 / (2 * (p : ℝ))) := by
      field_simp [hp.ne']
      nlinarith [le_of_lt hm_succ]
    rw [abs_le]
    constructor <;> nlinarith

/-- Helper for Theorem 1.3.6: coordinatewise midpoint bounds imply the corresponding `ℓ∞` bound
for the whole grid point. -/
theorem linftyNorm_sub_uniformGridPoint_le_of_forall_coord (p : ℕ+) {x : E}
    {α : Fin n → Fin p} {r : ℝ} (hr : 0 ≤ r)
    (hcoord : ∀ i, |x i - uniformGridPoint n p α i| ≤ r) :
    ‖x - uniformGridPoint n p α‖∞ ≤ r := by
  -- Rewrite the `ℓ∞` norm as the coordinate sup norm and apply the coordinatewise bound directly.
  rw [linftyNorm_eq_coordNorm]
  simpa [Real.norm_eq_abs] using
    (pi_norm_le_iff_of_nonneg hr).2 hcoord

/-- Every point of `[0,1]^n` is within `ℓ∞`-distance `1 / (2p)` of some midpoint grid point. -/
-- Proof sketch: choose in each coordinate the midpoint of the unique subinterval of the uniform
-- partition of `[0,1]` that contains that coordinate. The coordinatewise midpoint error is at
-- most `1 / (2p)`, and the `ℓ∞`-norm is the maximum of those coordinate errors.
theorem exists_uniformGrid_linfty_close (p : ℕ+) {x : E} (hx : x ∈ zeroOneBox n) :
    ∃ y ∈ uniformGrid n p, ‖x - y‖∞ ≤ 1 / (2 * (p : ℝ)) := by
  classical
  rw [mem_zeroOneBox_iff] at hx
  have hmid : ∀ i : Fin n,
      ∃ j : Fin p, |x i - ((((j : Fin p) : ℕ) : ℝ) + (1 / 2 : ℝ)) / (p : ℝ)| ≤
        1 / (2 * (p : ℝ)) :=
    fun i ↦ exists_midpoint_coordinate_close p (hx i)
  let α : Fin n → Fin p := fun i ↦ Classical.choose (hmid i)
  have hα : ∀ i : Fin n, |x i - uniformGridPoint n p α i| ≤ 1 / (2 * (p : ℝ)) := by
    -- The chosen midpoint in each coordinate defines the global grid index `α`.
    intro i
    simpa [α, uniformGridPoint_apply] using Classical.choose_spec (hmid i)
  refine ⟨uniformGridPoint n p α, ⟨α, rfl⟩, ?_⟩
  -- Aggregate the coordinatewise midpoint errors into the global `ℓ∞` bound.
  exact linftyNorm_sub_uniformGridPoint_le_of_forall_coord p (by positivity) hα

/- The theorem layer for item 1.3.6 has two surfaces:
the source-facing value-gap statement against `(zeroOneBoxProblem n f).optimalValue`, and the
derived bridge into the canonical owner predicate
`(zeroOneBoxProblem n f).IsApproximateMinimizer`. -/
-- Proof sketch: let `x ∈ B_n`. Choose a nearby midpoint grid point `y ∈ uniformGrid n p` using
-- `exists_uniformGrid_linfty_close`. Since `xBar` minimizes `f` on the grid and
-- `xBar ∈ uniformGrid n p`,
-- we have `f xBar ≤ f y`. Apply the Lipschitz estimate between `y` and `x`, using
-- `uniformGrid_subset_zeroOneBox` to see that `y ∈ [0,1]^n`, and conclude
-- `f xBar ≤ f x + L / (2p)` for every `x ∈ B_n`. This yields the claimed bound against
-- `(zeroOneBoxProblem n f).optimalValue`.
/-- Theorem 1.3.6: if `f ∈ 𝒫∞[n, L]` and the value `f xBar` is minimal on the midpoint grid of
mesh `1 / p`, then `f xBar` is at most `L / (2p)` above the canonical optimal value of the box
problem `min_{x ∈ B_n} f(x)`. -/
theorem uniformGrid_value_le_optimalValue_add_of_isMinOn
    (f : E → ℝ) (L : NNReal) (p : ℕ+) (xBar : E)
    (hf_lipschitz : f ∈ 𝒫∞[n, L])
    (hxBar_min : IsMinOn f (uniformGrid n p) xBar) :
    (f xBar : EReal) ≤ (zeroOneBoxProblem n f).optimalValue + (L : ℝ) / (2 * (p : ℝ)) := by
  let ε : ℝ := (L : ℝ) / (2 * (p : ℝ))
  have hxBar_le_add {x : E} (hx : x ∈ zeroOneBox n) :
      (f xBar : EReal) ≤ (f x : EReal) + ε := by
    rcases exists_uniformGrid_linfty_close p hx with ⟨y, hy_grid, hxy⟩
    have hxBar_le_y : f xBar ≤ f y := by
      rw [isMinOn_iff] at hxBar_min
      exact hxBar_min y hy_grid
    have hy_box : y ∈ zeroOneBox n :=
      uniformGrid_subset_zeroOneBox p hy_grid
    have hyx_dist :
        (L : ℝ) * ‖y - x‖∞ ≤ ε := by
      have hxy' : ‖y - x‖∞ ≤ 1 / (2 * (p : ℝ)) := by
        simpa [norm_sub_rev] using hxy
      have hL_nonneg : 0 ≤ (L : ℝ) := by
        exact_mod_cast L.2
      calc
        (L : ℝ) * ‖y - x‖∞ ≤ (L : ℝ) * (1 / (2 * (p : ℝ))) := by
          gcongr
        _ = ε := by
          simp [ε, div_eq_mul_inv]
    have hy_dist :
        |f y - f x| ≤ ε := by
      exact (abs_sub_le_mul_linftyNorm hf_lipschitz hy_box hx).trans hyx_dist
    have hy_le_x : f y ≤ f x + ε := by
      have hy_sub_x : f y - f x ≤ ε := (abs_sub_le_iff.mp hy_dist).1
      linarith
    have hxBar_le_x : f xBar ≤ f x + ε :=
      le_trans hxBar_le_y hy_le_x
    exact_mod_cast hxBar_le_x
  by_contra h
  have hgap : (zeroOneBoxProblem n f).optimalValue + ε < (f xBar : EReal) := by
    simpa [ε] using h
  have hopt_lt : (zeroOneBoxProblem n f).optimalValue < (f xBar : EReal) - ε := by
    exact (EReal.lt_sub_iff_add_lt (.inl (EReal.coe_ne_bot ε)) (.inl (EReal.coe_ne_top ε))).2 hgap
  rw [optimalValue_eq_sInf_image] at hopt_lt
  have himage_nonempty :
      ((fun x ↦ (zeroOneBoxProblem n f x : EReal)) ''
        (zeroOneBoxProblem n f).feasibleSet).Nonempty := by
    refine ⟨(f 0 : EReal), ?_⟩
    refine ⟨0, ?_, by simp⟩
    change (0 : E) ∈ zeroOneBox n
    exact zeroOneBox_zero_mem n
  rcases exists_lt_of_csInf_lt himage_nonempty hopt_lt with ⟨v, hv, hvlt⟩
  rcases hv with ⟨x, hx, rfl⟩
  have hxBar_le : (f xBar : EReal) ≤ (f x : EReal) + ε := by
    simpa [ε] using hxBar_le_add (by simpa using hx)
  have hlt : (f x : EReal) + ε < (f xBar : EReal) := by
    exact EReal.add_lt_of_lt_sub (by simpa [ε] using hvlt)
  exact (not_lt_of_ge hxBar_le hlt)

/-- Theorem 1.3.6 in the canonical approximate-minimizer owner language. -/
theorem uniformGrid_isApproximateMinimizer_of_isMinOn
    (f : E → ℝ) (L : NNReal) (p : ℕ+) (xBar : E)
    (hxBar : xBar ∈ uniformGrid n p)
    (hf_lipschitz : f ∈ 𝒫∞[n, L])
    (hxBar_min : IsMinOn f (uniformGrid n p) xBar) :
    (zeroOneBoxProblem n f).IsApproximateMinimizer ((L : ℝ) / (2 * (p : ℝ))) xBar := by
  rw [isApproximateMinimizer_iff]
  refine ⟨?_, uniformGrid_value_le_optimalValue_add_of_isMinOn f L p xBar hf_lipschitz hxBar_min⟩
  simpa using uniformGrid_subset_zeroOneBox p hxBar
