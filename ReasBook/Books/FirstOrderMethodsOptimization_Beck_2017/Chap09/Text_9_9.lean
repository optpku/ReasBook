/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_11
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_24
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_16
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_14
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_24
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_6
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp (toLp)

/-- The Euclidean upper bound on the unit simplex used for comparison with the entropy-based
mirror-descent bound, indexed by the positive Euclidean Lipschitz constant `L_{f,2}`. -/
def simplex_euclidean_upper_bound (Lf2 : PosReal) (N : ℕ) : ℝ :=
  Real.sqrt 2 * Lf2 / Real.sqrt (N + 1 : ℝ)

/-- The non-Euclidean mirror-descent upper bound on the unit simplex with the `ℓ_1` norm,
negative entropy mirror map, and uniform initialization `x⁰ = (1 / n)e`, indexed by the positive
sup-norm Lipschitz constant `L_{f,∞}`. -/
def simplex_non_euclidean_upper_bound (n : ℕ) (LfInf : PosReal) (N : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log (n : ℝ)) * LfInf / Real.sqrt (N + 1 : ℝ)

/-- The comparison ratio of the simplex non-Euclidean and Euclidean upper bounds for a positive
sup-norm constant `L_{f,∞}` and a positive Euclidean constant `L_{f,2}`. The positivity is part
of the input type, so the quotient is a genuine ratio rather than a totalized
division-by-zero expression. -/
def simplex_efficiency_ratio (n : ℕ) (LfInf Lf2 : PosReal) : ℝ :=
  Real.sqrt (Real.log (n : ℝ)) * LfInf / Lf2

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "E₁" => WithLp 1 (Fin n → ℝ)
local notation "Δ" => (toLp 2 '' (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)) : Set E)
local notation "Δ₁" =>
  (Set.preimage (WithLp.ofLp : E₁ → Fin n → ℝ) (stdSimplex ℝ (Fin n)) : Set E₁)
local notation "ωₑ" => negative_entropy_function n

/- Text 9.9 is `source-facing`: it compares the two textbook simplex mirror-descent upper bounds,
one coming from the Euclidean specialization in Text 9.8 and one coming from the entropy
specialization of the Chapter 9 fixed-horizon mirror-descent owner. The canonical upstream owners
already present in the repository are `uniform_simplex_point`, `negative_entropy_on_stdSimplex`,
`is_mirror_descent_trajectory`, and `fixed_iteration_objective`; this file keeps the textbook
closed forms and their comparison ratio as the reusable source-facing API. -/

-- Proof sketch: on the simplex, the negative-entropy Bregman distance from the uniform point
-- `x⁰ = (1 / n)e` is the Kullback-Leibler divergence relative to the uniform distribution, namely
-- `∑ i x_i log (n x_i)`, and this is bounded above by `log n`.
/-- On the simplex, the negative-entropy Bregman distance to the uniform point `x⁰ = (1 / n)e`
is bounded by `log n`. This is the simplex entropy diameter estimate `Θ₀ = log n`. -/
theorem negative_entropy_bregman_le_log_of_mem_simplex
    (hn : 0 < n) {x : E} (hx : x ∈ Δ) :
    B[ωₑ] x (uniform_simplex_point hn : E) ≤ Real.log (n : ℝ) := by
  rcases hx with ⟨x', hx', rfl⟩
  have hx_pre :
      toLp 2 x' ∈
        Set.preimage (WithLp.ofLp : E → Fin n → ℝ) (stdSimplex ℝ (Fin n)) := by
    simpa
  have huniform_pre :
      (uniform_simplex_point hn : E) ∈
        Set.preimage (WithLp.ofLp : E → Fin n → ℝ) (stdSimplex ℝ (Fin n)) := by
    rw [Set.mem_preimage, coe_uniform_simplex_point hn]
    constructor
    · intro i
      positivity
    · have hn_real_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hn
      simp [Finset.card_univ, Fintype.card_fin, hn_real_ne]
  have huniform_pos : ∀ i, 0 < (uniform_simplex_point hn : E) i := by
    intro i
    rw [coe_uniform_simplex_point hn]
    have hn_real : 0 < (n : ℝ) := by
      exact_mod_cast hn
    positivity
  have hkl :=
    negative_entropy_bregman_eq_kullbackLeibler
      (n := n) (x := toLp 2 x') (y := (uniform_simplex_point hn : E))
      hx_pre huniform_pre huniform_pos
  have hrewrite :
      ∑ i, (toLp 2 x') i * Real.log ((toLp 2 x') i / (uniform_simplex_point hn : E) i) =
        Real.log (n : ℝ) + ∑ i, x' i * Real.log (x' i) := by
    rw [coe_uniform_simplex_point hn]
    calc
      ∑ i, (toLp 2 x') i * Real.log ((toLp 2 x') i / (toLp 2 (fun _ : Fin n ↦ 1 / (n : ℝ))) i)
          = ∑ i, x' i * Real.log (x' i / (1 / (n : ℝ))) := by
              simp
      _ = ∑ i, (x' i * Real.log (x' i) + x' i * Real.log (n : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hxi : x' i = 0
            · simp [hxi]
            · have hn_real_ne : (n : ℝ) ≠ 0 := by
                exact_mod_cast Nat.ne_of_gt hn
              have hlog :
                  Real.log (x' i / (1 / (n : ℝ))) =
                    Real.log (x' i) + Real.log (n : ℝ) := by
                rw [show x' i / (1 / (n : ℝ)) = x' i * (n : ℝ) by field_simp [hn_real_ne]]
                rw [Real.log_mul hxi hn_real_ne]
              rw [hlog]
              ring
      _ = ∑ i, x' i * Real.log (x' i) + ∑ i, x' i * Real.log (n : ℝ) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ i, x' i * Real.log (x' i) + Real.log (n : ℝ) * ∑ i, x' i := by
            congr 1
            calc
              ∑ i, x' i * Real.log (n : ℝ) = ∑ i, Real.log (n : ℝ) * x' i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
              _ = Real.log (n : ℝ) * ∑ i, x' i := by
                    rw [Finset.mul_sum]
      _ = Real.log (n : ℝ) + ∑ i, x' i * Real.log (x' i) := by
            rw [hx'.2]
            ring
  have hentropy_nonpos : ∑ i, x' i * Real.log (x' i) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro i hi
    exact Real.mul_log_nonpos
      (mem_Icc_of_mem_stdSimplex hx' i).1
      (mem_Icc_of_mem_stdSimplex hx' i).2
  -- Rewrite the KL divergence against the uniform distribution and bound the entropy correction.
  calc
    B[ωₑ] (toLp 2 x') (uniform_simplex_point hn : E)
        = ∑ i, (toLp 2 x') i * Real.log ((toLp 2 x') i / (uniform_simplex_point hn : E) i) := hkl
    _ = Real.log (n : ℝ) + ∑ i, x' i * Real.log (x' i) := hrewrite
    _ ≤ Real.log (n : ℝ) := by
          linarith

/-- Helper for Text 9.9: membership in the Euclidean simplex image `Δ` is equivalent to the
coordinate vector lying in `stdSimplex ℝ (Fin n)`. -/
lemma memDelta_iff_ofLp_mem_stdSimplex {z : E} :
    z ∈ Δ ↔ z.ofLp ∈ stdSimplex ℝ (Fin n) := by
  constructor
  · intro hz
    rcases hz with ⟨z', hz', rfl⟩
    simpa
  · intro hz
    refine ⟨z.ofLp, hz, ?_⟩
    exact WithLp.toLp_ofLp (p := (2 : ENNReal)) z

/-- Helper for Text 9.9: every positive-stepsize prefix sum is strictly positive. -/
lemma simplexPositiveStepsizePrefixSum_pos
    {f : E → EReal} {x g : ℕ → E} {t : ℕ → ℝ}
    (h_traj :
      is_mirror_descent_trajectory
        (fun y ↦ (f y).toReal)
        (fun y ↦ (negative_entropy_function n y).toReal)
        Δ
        x
        g
        t)
    (N : ℕ) :
    0 < Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
  -- The initial positive stepsize already appears in every finite prefix.
  have hmem : 0 ∈ Finset.range (N + 1) := by
    simp
  have hle :
      t 0 ≤ Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
    simpa using
      (Finset.single_le_sum (fun k _ ↦ le_of_lt (h_traj.stepsize_pos k)) hmem)
  exact lt_of_lt_of_le (h_traj.stepsize_pos 0) hle

/-- Helper for Text 9.9: every iterate of the simplex entropy mirror-descent trajectory has
strictly positive coordinates. -/
lemma simplexMirrorDescentIterate_pos
    (hn : 0 < n) {f : E → EReal}
    {x g : ℕ → E} {t : ℕ → ℝ}
    (h_traj :
      is_mirror_descent_trajectory
        (fun y ↦ (f y).toReal)
        (fun y ↦ (negative_entropy_function n y).toReal)
        Δ
        x
        g
        t)
    (hx0 : x 0 = (uniform_simplex_point hn : E)) :
    ∀ k i, 0 < (x k).ofLp i := by
  intro k
  induction k with
  | zero =>
      intro i
      -- The uniform initialization has every coordinate equal to `1 / n`.
      rw [hx0, coe_uniform_simplex_point hn]
      have hn_real : 0 < (n : ℝ) := by
        exact_mod_cast hn
      positivity
  | succ k ih =>
      intro i
      have hxk_simplex : (x k).ofLp ∈ stdSimplex ℝ (Fin n) :=
        (memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp (h_traj.mem_feasible_set k)
      have hxkNext_simplex : (x (k + 1)).ofLp ∈ stdSimplex ℝ (Fin n) :=
        (memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp (h_traj.mem_feasible_set (k + 1))
      have hmin_pre :
        IsMinOn
          (mirror_descent_update_objective
              (fun z : E ↦ (negative_entropy_function n z).toReal)
              (x k)
              (g k)
              (t k))
            (Set.preimage (WithLp.ofLp : E → Fin n → ℝ) (stdSimplex ℝ (Fin n)))
            (x (k + 1)) := by
        have hmin_image := h_traj.isMinOn k
        -- Rewrite the simplex constraint to the `Text_9_6` preimage form.
        rw [isMinOn_iff] at hmin_image ⊢
        intro y hy
        exact hmin_image y ((memDelta_iff_ofLp_mem_stdSimplex (n := n)).2 hy)
      have hsoftmax :
          (x (k + 1)).ofLp =
            softmax_point
              (fun j ↦ Real.log ((x k).ofLp j) - t k * g k j) := by
        -- Identify the next iterate with the canonical softmax point from Text 9.6.
        exact
          (mirror_descent_step_eq_exponentiated_gradient
            (n := n)
            (x := x k)
            (g := g k)
            (xNext := x (k + 1))
            (t := t k)
            ((memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp (h_traj.mem_feasible_set k))
            (ih)).mp ⟨by simpa [Set.mem_preimage] using hxkNext_simplex, hmin_pre⟩
      -- The softmax characterization exposes strict positivity coordinatewise.
      simpa [hsoftmax] using
        softmax_point_pos
          (fun j ↦ Real.log ((x k).ofLp j) - t k * g k j)
          i

/-- Helper for Text 9.9: the step optimality inequality rewrites into the one-step Bregman-drop
comparison against any feasible comparator `u ∈ Δ`. -/
lemma simplexMirrorDescentObjectiveComparison
    (hn : 0 < n)
    {f : E → EReal}
    {x g : ℕ → E} {t : ℕ → ℝ}
    (h_traj :
      is_mirror_descent_trajectory
        (fun y ↦ (f y).toReal)
        (fun y ↦ (negative_entropy_function n y).toReal)
        Δ
        x
        g
        t)
    (hx0 : x 0 = (uniform_simplex_point hn : E))
    (k : ℕ) {u : E} (hu : u ∈ Δ) :
    t k * inner ℝ (g k) (x (k + 1) - u) ≤
      B[ωₑ] u (x k) - B[ωₑ] u (x (k + 1)) - B[ωₑ] (x (k + 1)) (x k) := by
  have hxk_simplex : (x k).ofLp ∈ stdSimplex ℝ (Fin n) :=
    (memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp (h_traj.mem_feasible_set k)
  have hxkNext_simplex : (x (k + 1)).ofLp ∈ stdSimplex ℝ (Fin n) :=
    (memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp (h_traj.mem_feasible_set (k + 1))
  have hu_simplex : u.ofLp ∈ stdSimplex ℝ (Fin n) :=
    (memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp hu
  have hxk_pre :
      x k ∈ Set.preimage (WithLp.ofLp : E → Fin n → ℝ) (stdSimplex ℝ (Fin n)) := by
    simpa [Set.mem_preimage] using hxk_simplex
  have hxkNext_pre :
      x (k + 1) ∈ Set.preimage (WithLp.ofLp : E → Fin n → ℝ) (stdSimplex ℝ (Fin n)) := by
    simpa [Set.mem_preimage] using hxkNext_simplex
  have hu_pre :
      u ∈ Set.preimage (WithLp.ofLp : E → Fin n → ℝ) (stdSimplex ℝ (Fin n)) := by
    simpa [Set.mem_preimage] using hu_simplex
  have hxk_pos := simplexMirrorDescentIterate_pos (n := n) hn h_traj hx0 k
  have hxkNext_pos := simplexMirrorDescentIterate_pos (n := n) hn h_traj hx0 (k + 1)
  have hsoftmax :
      (x (k + 1)).ofLp =
        softmax_point
          (fun i ↦ Real.log ((x k).ofLp i) - t k * g k i) := by
    have hmin_pre :
        IsMinOn
          (mirror_descent_update_objective
            (fun z : E ↦ (negative_entropy_function n z).toReal)
            (x k)
            (g k)
            (t k))
          (Set.preimage (WithLp.ofLp : E → Fin n → ℝ) (stdSimplex ℝ (Fin n)))
          (x (k + 1)) := by
      have hmin_image := h_traj.isMinOn k
      rw [isMinOn_iff] at hmin_image ⊢
      intro y hy
      exact hmin_image y ((memDelta_iff_ofLp_mem_stdSimplex (n := n)).2 hy)
    exact
      (mirror_descent_step_eq_exponentiated_gradient
        (n := n)
        (x := x k)
        (g := g k)
        (xNext := x (k + 1))
        (t := t k)
        hxk_simplex
        hxk_pos).mp
        ⟨hxkNext_pre, hmin_pre⟩
  have huxk :=
    negative_entropy_bregman_eq_kullbackLeibler
      (n := n) (x := u) (y := x k) hu_pre hxk_pre hxk_pos
  have huxkNext :=
    negative_entropy_bregman_eq_kullbackLeibler
      (n := n) (x := u) (y := x (k + 1)) hu_pre hxkNext_pre hxkNext_pos
  have hxkNextxk :=
    negative_entropy_bregman_eq_kullbackLeibler
      (n := n) (x := x (k + 1)) (y := x k) hxkNext_pre hxk_pre hxk_pos
  let y : Fin n → ℝ := fun i ↦ Real.log ((x k).ofLp i) - t k * g k i
  let c : ℝ := Real.log (∑ j, Real.exp (y j))
  have hlogRatio :
      ∀ i : Fin n,
        Real.log (((x (k + 1)).ofLp i) / ((x k).ofLp i)) = -t k * g k i - c := by
    intro i
    rw [hsoftmax]
    rw [Real.log_div (softmax_point_pos y i).ne' (hxk_pos i).ne']
    rw [softmax_point_log (y := y) i]
    simp [y, c]
    ring
  have hterm :
      ∀ i : Fin n,
        u.ofLp i * Real.log (u.ofLp i / (x k).ofLp i) -
            u.ofLp i * Real.log (u.ofLp i / (x (k + 1)).ofLp i) -
            (x (k + 1)).ofLp i * Real.log ((x (k + 1)).ofLp i / (x k).ofLp i) =
          (u.ofLp i - (x (k + 1)).ofLp i) *
            Real.log (((x (k + 1)).ofLp i) / ((x k).ofLp i)) := by
    intro i
    by_cases hui : u.ofLp i = 0
    · simp [hui]
    · rw [Real.log_div hui (hxk_pos i).ne', Real.log_div hui (hxkNext_pos i).ne']
      rw [Real.log_div (hxkNext_pos i).ne' (hxk_pos i).ne']
      ring
  have hsum_zero : ∑ i, ((x (k + 1)).ofLp i - u.ofLp i) = 0 := by
    rw [Finset.sum_sub_distrib, hxkNext_simplex.2, hu_simplex.2]
    ring
  have hinner :
      inner ℝ (g k) (x (k + 1) - u) =
        ∑ i, g k i * ((x (k + 1)).ofLp i - u.ofLp i) := by
    calc
      inner ℝ (g k) (x (k + 1) - u) =
          dotProduct (g k).ofLp (x (k + 1) - u).ofLp := by
            simpa [dotProduct_comm] using
              (EuclideanSpace.inner_toLp_toLp (g k).ofLp (x (k + 1) - u).ofLp)
      _ = ∑ i, g k i * ((x (k + 1)).ofLp i - u.ofLp i) := by
            simp [dotProduct]
  have hthreePoint :
      B[ωₑ] u (x k) - B[ωₑ] u (x (k + 1)) - B[ωₑ] (x (k + 1)) (x k) =
        t k * inner ℝ (g k) (x (k + 1) - u) := by
    calc
      B[ωₑ] u (x k) - B[ωₑ] u (x (k + 1)) - B[ωₑ] (x (k + 1)) (x k)
          = ∑ i,
              (u.ofLp i * Real.log (u.ofLp i / (x k).ofLp i) -
                u.ofLp i * Real.log (u.ofLp i / (x (k + 1)).ofLp i) -
                (x (k + 1)).ofLp i * Real.log ((x (k + 1)).ofLp i / (x k).ofLp i)) := by
              rw [huxk, huxkNext, hxkNextxk, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      _ = ∑ i,
            (u.ofLp i - (x (k + 1)).ofLp i) *
              Real.log (((x (k + 1)).ofLp i) / ((x k).ofLp i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hterm i
      _ = ∑ i, (u.ofLp i - (x (k + 1)).ofLp i) * (-t k * g k i - c) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hlogRatio i]
      _ = ∑ i,
            ((t k * g k i) * ((x (k + 1)).ofLp i - u.ofLp i) +
              c * ((x (k + 1)).ofLp i - u.ofLp i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ =
          ∑ i, (t k * g k i) * ((x (k + 1)).ofLp i - u.ofLp i) +
            ∑ i, c * ((x (k + 1)).ofLp i - u.ofLp i) := by
              rw [Finset.sum_add_distrib]
      _ =
          ∑ i, (t k * g k i) * ((x (k + 1)).ofLp i - u.ofLp i) +
            c * ∑ i, ((x (k + 1)).ofLp i - u.ofLp i) := by
              rw [Finset.mul_sum]
      _ = ∑ i, (t k * g k i) * ((x (k + 1)).ofLp i - u.ofLp i) := by
            rw [hsum_zero]
            ring
      _ = t k * ∑ i, g k i * ((x (k + 1)).ofLp i - u.ofLp i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = t k * inner ℝ (g k) (x (k + 1) - u) := by
            rw [hinner]
  linarith [hthreePoint]

/-- Helper for Text 9.9: the Euclidean pairing is controlled by the coordinate `ℓ_∞/ℓ₁` duality
bound on `ℝ^n`. -/
lemma simplexInner_le_linfty_mul_l1 (v d : E) :
    inner ℝ v d ≤ ‖toLp ⊤ (fun i ↦ v i)‖ * ‖toLp 1 (fun i ↦ d i)‖ := by
  calc
    inner ℝ v d = dotProduct v.ofLp d.ofLp := by
      simpa [dotProduct_comm] using (EuclideanSpace.inner_toLp_toLp v.ofLp d.ofLp)
    _ ≤ ∑ i, |v i| * |d i| := by
      refine Finset.sum_le_sum ?_
      intro i hi
      simpa [abs_mul] using le_abs_self (v i * d i)
    _ ≤ ∑ i, ‖toLp ⊤ (fun j ↦ v j)‖ * |d i| := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (by simpa using abs_le_pi_norm (fun j ↦ v j) i)
        (abs_nonneg _)
    _ = ‖toLp ⊤ (fun i ↦ v i)‖ * ∑ i, |d i| := by
      rw [Finset.mul_sum]
    _ = ‖toLp ⊤ (fun i ↦ v i)‖ * ‖toLp 1 (fun i ↦ d i)‖ := by
      rw [PiLp.norm_eq_sum (p := (1 : ENNReal)) (by norm_num)]
      · simp

/-- Helper for Text 9.9: the affine functional with coordinates `log (y_i) + 1` on the `ℓ₁`
simplex model. -/
private def entropySupportFunctional (y : Fin n → ℝ) : Module.Dual ℝ E₁ :=
  ∑ i, (Real.log (y i) + 1) •
    (PiLp.proj 1 (fun _ : Fin n ↦ ℝ) i : E₁ →L[ℝ] ℝ)

/-- Helper for Text 9.9: the effective domain of `z ↦ negative_entropy_on_stdSimplex n z.ofLp`
on `E₁` is exactly the simplex preimage `Δ₁`. -/
private lemma memEffectiveDomainNegativeEntropyIff {z : E₁} :
    z ∈ effective_domain (fun w : E₁ ↦ negative_entropy_on_stdSimplex n w.ofLp) ↔ z ∈ Δ₁ := by
  change negative_entropy_on_stdSimplex n z.ofLp < ⊤ ↔ z.ofLp ∈ stdSimplex ℝ (Fin n)
  by_cases hz : z.ofLp ∈ stdSimplex ℝ (Fin n) <;>
    simp [negative_entropy_on_stdSimplex, hz]

/-- Helper for Text 9.9: evaluating the entropy support functional is the expected coordinate
pairing. -/
private lemma entropySupportFunctional_apply (y : Fin n → ℝ) (z : E₁) :
    entropySupportFunctional (n := n) y z =
      ∑ i, (Real.log (y i) + 1) * z.ofLp i := by
  -- Expand the coordinate functional once and simplify the projection evaluations.
  simp [entropySupportFunctional]

/-- Helper for Text 9.9: the scalar entropy `u log u` lies above its tangent line at every
positive base point. -/
private lemma entropyScalar_support
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) :
    v * Real.log v + (Real.log v + 1) * (u - v) ≤ u * Real.log u := by
  by_cases hu_zero : u = 0
  · -- The zero endpoint contributes no entropy, so only the negative tangent intercept remains.
    subst hu_zero
    have hleft : v * Real.log v + (Real.log v + 1) * (0 - v) = -v := by
      ring_nf
    rw [hleft]
    linarith
  · have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu_zero)
    have hratio :
        1 - (u / v)⁻¹ ≤ Real.log (u / v) :=
      Real.one_sub_inv_le_log_of_pos (div_pos hu_pos hv)
    have hmul :
        u * (1 - (u / v)⁻¹) ≤ u * Real.log (u / v) := by
      exact mul_le_mul_of_nonneg_left hratio hu
    have hleft : u * (1 - (u / v)⁻¹) = u - v := by
      field_simp [hu_pos.ne', hv.ne']
    have hright : u * Real.log (u / v) = u * Real.log u - u * Real.log v := by
      rw [Real.log_div hu_pos.ne' hv.ne']
      ring
    -- Rewrite the logarithmic ratio inequality back to the tangent-line form.
    rw [hleft, hright] at hmul
    linarith

/-- Helper for Text 9.9: at a strictly positive simplex point, the coordinate entropy tangent
defines a genuine owner-side subgradient on the `ℓ₁` simplex model. -/
private lemma entropySupportFunctional_mem_subdifferential
    {y : E₁} (hy : y ∈ Δ₁) (hy_pos : ∀ i, 0 < y.ofLp i) :
    entropySupportFunctional (n := n) y.ofLp ∈
      subdifferential (fun z : E₁ ↦ negative_entropy_on_stdSimplex n z.ofLp) y := by
  have hy_simplex : y.ofLp ∈ stdSimplex ℝ (Fin n) := by
    simpa [Set.mem_preimage] using hy
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  constructor
  · -- The simplex branch is exactly the effective domain of the entropy extension.
    exact (memEffectiveDomainNegativeEntropyIff (n := n)).2 hy
  · intro z hz
    have hz_simplex : z.ofLp ∈ stdSimplex ℝ (Fin n) := by
      simpa [Set.mem_preimage] using
        (memEffectiveDomainNegativeEntropyIff (n := n) (z := z)).1 hz
    have hcoord :
        ∀ i : Fin n,
          y.ofLp i * Real.log (y.ofLp i) +
              (Real.log (y.ofLp i) + 1) * (z.ofLp i - y.ofLp i) ≤
            z.ofLp i * Real.log (z.ofLp i) := by
      intro i
      exact
        entropyScalar_support
          ((mem_Icc_of_mem_stdSimplex hz_simplex i).1)
          (hy_pos i)
    have hsum :
        ∑ i, y.ofLp i * Real.log (y.ofLp i) +
            entropySupportFunctional (n := n) y.ofLp (z - y) ≤
          ∑ i, z.ofLp i * Real.log (z.ofLp i) := by
      calc
        ∑ i, y.ofLp i * Real.log (y.ofLp i) +
            entropySupportFunctional (n := n) y.ofLp (z - y)
            =
              ∑ i,
                (y.ofLp i * Real.log (y.ofLp i) +
                  (Real.log (y.ofLp i) + 1) * (z.ofLp i - y.ofLp i)) := by
                rw [entropySupportFunctional_apply]
                simp [Finset.sum_add_distrib]
        _ ≤ ∑ i, z.ofLp i * Real.log (z.ofLp i) := by
              exact Finset.sum_le_sum fun i _ ↦ hcoord i
    -- Rewrite the owner-side entropy to its simplex branch and package the real inequality in
    -- `EReal`.
    rw [negative_entropy_on_stdSimplex_of_mem hz_simplex]
    rw [negative_entropy_on_stdSimplex_of_mem hy_simplex, ge_iff_le, ← EReal.coe_add]
    exact EReal.coe_le_coe hsum

/-- Helper for Text 9.9: the simplex negative entropy satisfies the `ℓ₁` lower-support inequality
with the strong-convexity quadratic correction at a positive base point. -/
private lemma negativeEntropyLowerSupport_l1_onSimplex
    {x y : E} (hx : x ∈ Δ) (hy : y ∈ Δ) (hy_pos : ∀ i, 0 < y i) :
    (negative_entropy_on_stdSimplex n x.ofLp).toReal ≥
      (negative_entropy_on_stdSimplex n y.ofLp).toReal +
        ∑ i, (Real.log (y i) + 1) * (x i - y i) +
        (1 / 2 : ℝ) * ‖toLp 1 (fun i ↦ x i - y i)‖ ^ (2 : ℕ) := by
  let f : E₁ → EReal := fun z ↦ negative_entropy_on_stdSimplex n z.ofLp
  let x₁ : E₁ := toLp 1 x.ofLp
  let y₁ : E₁ := toLp 1 y.ofLp
  have hx_simplex : x.ofLp ∈ stdSimplex ℝ (Fin n) :=
    (memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp hx
  have hy_simplex : y.ofLp ∈ stdSimplex ℝ (Fin n) :=
    (memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp hy
  have hdomain : effective_domain f = Δ₁ := by
    ext z
    simpa [f] using (memEffectiveDomainNegativeEntropyIff (n := n) (z := z))
  have hx₁ : x₁ ∈ effective_domain f := by
    -- Transport the Euclidean simplex point to the canonical `WithLp 1` simplex surface.
    simpa [f, x₁] using (memEffectiveDomainNegativeEntropyIff (n := n) (z := x₁)).2
      (by simpa [Set.mem_preimage, x₁] using hx_simplex)
  have hy₁ : y₁ ∈ effective_domain f := by
    simpa [f, y₁] using (memEffectiveDomainNegativeEntropyIff (n := n) (z := y₁)).2
      (by simpa [Set.mem_preimage, y₁] using hy_simplex)
  have hy₁_simplex : y₁ ∈ Δ₁ := by
    simpa [Set.mem_preimage, y₁] using hy_simplex
  have hy₁_pos : ∀ i, 0 < y₁.ofLp i := by
    intro i
    simpa [y₁] using hy_pos i
  have hg :
      entropySupportFunctional (n := n) y.ofLp ∈ subdifferential f y₁ := by
      simpa [f, y₁] using
        (entropySupportFunctional_mem_subdifferential (n := n) hy₁_simplex hy₁_pos)
  have hne_bot : ∀ z : E₁, f z ≠ ⊥ := by
    intro z
    by_cases hz : z.ofLp ∈ stdSimplex ℝ (Fin n)
    · simp [f, negative_entropy_on_stdSimplex, hz]
    · simp [f, negative_entropy_on_stdSimplex, hz]
  have hstrong :
      StrongConvexOn (effective_domain f) 1 (fun z ↦ (f z).toReal) := by
    -- Route correction: use Proposition 5.14 directly on the canonical `WithLp 1` simplex model.
    rw [hdomain]
    simpa [f] using
      (negative_entropy_on_stdSimplex_is_one_strongly_convex_l1 (n := n))
  have hquad :
      f x₁ ≥
        f y₁ +
          ((entropySupportFunctional (n := n) y.ofLp (x₁ - y₁) +
              (1 / 2 : ℝ) * ‖x₁ - y₁‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    exact
      (subgradientQuadraticLowerBound_of_strongConvexOn
        (f := f) (σ := (1 : ℝ)) (hσ := by norm_num) hne_bot hstrong).apply
        y₁ hg x₁ hx₁
  have hquad_real :
      (negative_entropy_on_stdSimplex n x.ofLp).toReal ≥
        (negative_entropy_on_stdSimplex n y.ofLp).toReal +
          (entropySupportFunctional (n := n) y.ofLp (x₁ - y₁) +
            (1 / 2 : ℝ) * ‖x₁ - y₁‖ ^ (2 : ℕ)) := by
    have hquad' :
        ((((negative_entropy_on_stdSimplex n y.ofLp).toReal +
            (entropySupportFunctional (n := n) y.ofLp (x₁ - y₁) +
              (1 / 2 : ℝ) * ‖x₁ - y₁‖ ^ (2 : ℕ)) : ℝ) : EReal)) ≤
          ((((negative_entropy_on_stdSimplex n x.ofLp).toReal : ℝ) : EReal)) := by
      exact ge_iff_le.mp (by simpa [f, x₁, y₁, hx_simplex, hy_simplex, EReal.coe_add,
        negative_entropy_on_stdSimplex] using hquad)
    exact EReal.coe_le_coe_iff.mp hquad'
  -- Rewrite the transported subgradient pairing and norm back on the Euclidean simplex surface.
  calc
    (negative_entropy_on_stdSimplex n x.ofLp).toReal ≥
        (negative_entropy_on_stdSimplex n y.ofLp).toReal +
          (entropySupportFunctional (n := n) y.ofLp (x₁ - y₁) +
            (1 / 2 : ℝ) * ‖x₁ - y₁‖ ^ (2 : ℕ)) := hquad_real
    _ =
        (negative_entropy_on_stdSimplex n y.ofLp).toReal +
          ∑ i, (Real.log (y i) + 1) * (x i - y i) +
          (1 / 2 : ℝ) * ‖toLp 1 (fun i ↦ x i - y i)‖ ^ (2 : ℕ) := by
            have hsupportApply :
                entropySupportFunctional (n := n) y.ofLp (x₁ - y₁) =
                  ∑ i, (Real.log (y i) + 1) * (x i - y i) := by
              rw [entropySupportFunctional_apply]
              rw [← WithLp.toLp_sub (p := (1 : ENNReal)) x.ofLp y.ofLp]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rfl
            have hnorm :
                ‖x₁ - y₁‖ ^ (2 : ℕ) = ‖toLp 1 (fun i ↦ x i - y i)‖ ^ (2 : ℕ) := by
              rw [← WithLp.toLp_sub (p := (1 : ENNReal)) x.ofLp y.ofLp]
              rfl
            rw [hsupportApply, hnorm]
            ring

/-- Helper for Text 9.9: simplex negative-entropy Bregman distance controls the squared `ℓ₁`
displacement from a positive base point. -/
lemma negativeEntropyBregman_ge_halfL1Sq_of_memSimplex
    {x y : E} (hx : x ∈ Δ) (hy : y ∈ Δ) (hy_pos : ∀ i, 0 < y i) :
    (1 / 2 : ℝ) * ‖toLp 1 (fun i ↦ x i - y i)‖ ^ (2 : ℕ) ≤ B[ωₑ] x y := by
  have hx_pre :
      x ∈ Set.preimage (WithLp.ofLp : E → Fin n → ℝ) (stdSimplex ℝ (Fin n)) := by
    simpa [Set.mem_preimage] using (memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp hx
  have hy_pre :
      y ∈ Set.preimage (WithLp.ofLp : E → Fin n → ℝ) (stdSimplex ℝ (Fin n)) := by
    simpa [Set.mem_preimage] using (memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp hy
  have hsupport :=
    negativeEntropyLowerSupport_l1_onSimplex (n := n) hx hy hy_pos
  have hhalf_le :
      (1 / 2 : ℝ) * ‖toLp 1 (fun i ↦ x i - y i)‖ ^ (2 : ℕ) ≤
        (negative_entropy_on_stdSimplex n x.ofLp).toReal -
          (negative_entropy_on_stdSimplex n y.ofLp).toReal -
          ∑ i, (Real.log (y i) + 1) * (x i - y i) := by
    -- Rearranging the lower-support inequality isolates the quadratic correction.
    linarith
  have hx_nonneg : ∀ i, 0 ≤ x i := by
    intro i
    exact (mem_Icc_of_mem_stdSimplex ((memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp hx) i).1
  have hy_nonneg : ∀ i, 0 ≤ y i := by
    intro i
    exact (mem_Icc_of_mem_stdSimplex ((memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp hy) i).1
  have coeRealSum (r : Fin n → ℝ) :
      (((∑ i, r i : ℝ)) : EReal) = ∑ i, (((r i : ℝ)) : EReal) := by
    refine Finset.induction_on Finset.univ ?_ ?_
    · simp
    · intro i s hi hs
      simp [Finset.sum_insert, hi, hs, EReal.coe_add]
  -- Route correction: after the `WithLp 1` lower-support bridge is established, the Chapter 9
  -- Bregman statement is just the existing expanded entropy identity.
  have hx_toReal :
      (negative_entropy_on_stdSimplex n x.ofLp).toReal = (ωₑ x).toReal := by
    rw [negative_entropy_on_stdSimplex_toReal_of_mem
      ((memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp hx)]
    have hωx :
        ωₑ x = (((∑ i, x i * Real.log (x i) : ℝ)) : EReal) := by
      rw [negative_entropy_function_apply]
      calc
        ∑ i, negative_entropy_scalar (x i) = ∑ i, (((x i * Real.log (x i) : ℝ)) : EReal) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [negative_entropy_scalar_of_nonneg (hx_nonneg i)]
        _ = (((∑ i, x i * Real.log (x i) : ℝ)) : EReal) := by
          symm
          exact coeRealSum (fun i ↦ x i * Real.log (x i))
    rw [hωx]
    simp
  have hy_toReal :
      (negative_entropy_on_stdSimplex n y.ofLp).toReal = (ωₑ y).toReal := by
    rw [negative_entropy_on_stdSimplex_toReal_of_mem
      ((memDelta_iff_ofLp_mem_stdSimplex (n := n)).mp hy)]
    have hωy :
        ωₑ y = (((∑ i, y i * Real.log (y i) : ℝ)) : EReal) := by
      rw [negative_entropy_function_apply]
      calc
        ∑ i, negative_entropy_scalar (y i) = ∑ i, (((y i * Real.log (y i) : ℝ)) : EReal) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [negative_entropy_scalar_of_nonneg (hy_nonneg i)]
        _ = (((∑ i, y i * Real.log (y i) : ℝ)) : EReal) := by
          symm
          exact coeRealSum (fun i ↦ y i * Real.log (y i))
    rw [hωy]
    simp
  calc
    (1 / 2 : ℝ) * ‖toLp 1 (fun i ↦ x i - y i)‖ ^ (2 : ℕ) ≤
        (ωₑ x).toReal - (ωₑ y).toReal -
          ∑ i, (Real.log (y i) + 1) * (x i - y i) := by
            simpa [hx_toReal, hy_toReal] using hhalf_le
    _ = ∑ i, x i * Real.log (x i / y i) := by
          exact
            negative_entropy_bregman_eq_kullbackLeibler_expanded
              (n := n) (x := x) (y := y) hx_pre hy_pre hy_pos
    _ = B[ωₑ] x y := by
          symm
          exact negative_entropy_bregman_eq_kullbackLeibler
            (n := n) (x := x) (y := y) hx_pre hy_pre hy_pos

/-- Helper for Text 9.9: the simplex entropy step displacement term is bounded by the one-step
Bregman correction plus the realized `ℓ_∞` norm square. -/
lemma simplexNegativeEntropyStepDisplacement_le_bregmanCorrection
    (hn : 0 < n) {f : E → EReal}
    {x g : ℕ → E} {t : ℕ → ℝ}
    (h_traj :
      is_mirror_descent_trajectory
        (fun y ↦ (f y).toReal)
        (fun y ↦ (negative_entropy_function n y).toReal)
        Δ
        x
        g
        t)
    (hx0 : x 0 = (uniform_simplex_point hn : E))
    (k : ℕ) :
    t k * inner ℝ (g k) (x k - x (k + 1)) ≤
      B[ωₑ] (x (k + 1)) (x k) +
        ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2 := by
  have hxk_simplex : x k ∈ Δ := h_traj.mem_feasible_set k
  have hxkNext_simplex : x (k + 1) ∈ Δ := h_traj.mem_feasible_set (k + 1)
  have hxk_pos := simplexMirrorDescentIterate_pos (n := n) hn h_traj hx0 k
  let a : ℝ := ‖toLp 1 (fun i ↦ x k i - x (k + 1) i)‖
  let b : ℝ := ‖toLp ⊤ (fun i ↦ g k i)‖
  have hl1_symm :
      ‖toLp 1 (fun i ↦ x (k + 1) i - x k i)‖ =
        ‖toLp 1 (fun i ↦ x k i - x (k + 1) i)‖ := by
    have hfun :
        (fun i ↦ x (k + 1) i - x k i) =
          fun i ↦ -(x k i - x (k + 1) i) := by
      funext i
      ring
    have hneg :
        toLp 1 (fun i ↦ x (k + 1) i - x k i) =
          -toLp 1 (fun i ↦ x k i - x (k + 1) i) := by
      ext i
      simp
    rw [hneg]
    simp
  have hbreg :
      (1 / 2 : ℝ) * a ^ (2 : ℕ) ≤ B[ωₑ] (x (k + 1)) (x k) := by
    -- Use the entropy Bregman lower bound at the current positive iterate `x k`.
    simpa [a, hl1_symm] using
      negativeEntropyBregman_ge_halfL1Sq_of_memSimplex
        (n := n) hxkNext_simplex hxk_simplex hxk_pos
  have hpair :
      inner ℝ (g k) (x k - x (k + 1)) ≤ b * a := by
    -- Bound the mixed term by the `ℓ_∞/ℓ₁` dual pairing estimate.
    simpa [a, b] using
      simplexInner_le_linfty_mul_l1 (g k) (x k - x (k + 1))
  have hyoung :
      t k * (b * a) ≤ (1 / 2 : ℝ) * a ^ (2 : ℕ) + ((t k) ^ (2 : ℕ) * b ^ (2 : ℕ)) / 2 := by
    have hsq_nonneg : 0 ≤ (a - t k * b) ^ (2 : ℕ) := sq_nonneg (a - t k * b)
    nlinarith
  -- Combine the dual-pairing bound with Young's inequality and the Bregman lower bound.
  calc
    t k * inner ℝ (g k) (x k - x (k + 1)) ≤ t k * (b * a) := by
      have ht_nonneg : 0 ≤ t k := le_of_lt (h_traj.stepsize_pos k)
      exact mul_le_mul_of_nonneg_left hpair ht_nonneg
    _ ≤ (1 / 2 : ℝ) * a ^ (2 : ℕ) + ((t k) ^ (2 : ℕ) * b ^ (2 : ℕ)) / 2 := hyoung
    _ ≤ B[ωₑ] (x (k + 1)) (x k) + ((t k) ^ (2 : ℕ) * b ^ (2 : ℕ)) / 2 := by
      linarith
    _ = B[ωₑ] (x (k + 1)) (x k) +
          ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2 := by
        simp [b]

/-- Helper for Text 9.9: summing the simplex one-step inequality should give the finite-horizon
running-best gap bound with the realized `ℓ_∞` correction term. -/
lemma simplexBregmanDifference_sum_range
    {x : ℕ → E} (xStar : E) (N : ℕ) :
    Finset.sum (Finset.range (N + 1))
      (fun k ↦ B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1))) =
        B[ωₑ] xStar (x 0) - B[ωₑ] xStar (x (N + 1)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      calc
        (Finset.sum (Finset.range (N + 1))
            (fun k ↦ B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1)))) +
            (B[ωₑ] xStar (x (N + 1)) - B[ωₑ] xStar (x (N + 2)))
            =
              (B[ωₑ] xStar (x 0) - B[ωₑ] xStar (x (N + 1))) +
                (B[ωₑ] xStar (x (N + 1)) - B[ωₑ] xStar (x (N + 2))) := by
                  rw [ih]
        _ = B[ωₑ] xStar (x 0) - B[ωₑ] xStar (x (N + 2)) := by
              ring

/-- Helper for Text 9.9: summing the simplex one-step inequality should give the finite-horizon
running-best gap bound with the realized `ℓ_∞` correction term. -/
lemma simplexNegativeEntropyBestGapLeWithNormCorrection
    (hn : 0 < n) {f : E → EReal} {XStar : Set E} {fOpt : ℝ}
    (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
    {x g : ℕ → E} {t : ℕ → ℝ}
    (h_traj :
      is_mirror_descent_trajectory
        (fun y ↦ (f y).toReal)
        (fun y ↦ (negative_entropy_function n y).toReal)
        Δ
        x
        g
        t)
    (hx0 : x 0 = (uniform_simplex_point hn : E))
    {xStar : E} (hxStar : xStar ∈ XStar)
    (N : ℕ) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      (B[ωₑ] xStar (x 0) +
          (1 / 2) *
            Finset.sum (Finset.range (N + 1))
              (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ))) /
        Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
  have hxStar_data : xStar ∈ Δ ∧ IsMinOn f Δ xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxStar_value :
      (f xStar).toReal = fOpt :=
    optimal_point_toReal_eq_fOpt h_problem hxStar
  have hpointwise :
      ∀ k ∈ Finset.range (N + 1),
        t k * ((f (x k)).toReal - fOpt) ≤
          B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1)) +
            ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2 := by
    intro k hk
    have hgap :
        (f (x k)).toReal - fOpt ≤ inner ℝ (g k) (x k - xStar) := by
      have hsub := h_traj.subgradient_mem k
      rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
        mem_subdifferential, is_subgradient_at_coe_iff] at hsub
      -- The selected Euclidean subgradient bounds the current optimality gap by the pairing
      -- toward the chosen optimal point `xStar`.
      have hpointwise_gap :
          (f xStar).toReal ≥ (f (x k)).toReal + inner ℝ (g k) (xStar - x k) := hsub xStar
      have hreverse :
          inner ℝ (g k) (xStar - x k) = -inner ℝ (g k) (x k - xStar) := by
        rw [show xStar - x k = -(x k - xStar) by abel, inner_neg_right]
      rw [hxStar_value] at hpointwise_gap
      nlinarith [hpointwise_gap, hreverse]
    have hforward :
        t k * inner ℝ (g k) (x (k + 1) - xStar) ≤
          B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1)) - B[ωₑ] (x (k + 1)) (x k) := by
      -- The simplex mirror-descent minimizer inequality gives the forward Bregman drop.
      simpa using simplexMirrorDescentObjectiveComparison
        (n := n) (hn := hn) (h_traj := h_traj) (hx0 := hx0) k hxStar_data.1
    have hdisplacement :
        t k * inner ℝ (g k) (x k - x (k + 1)) ≤
          B[ωₑ] (x (k + 1)) (x k) +
            ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2 :=
      simplexNegativeEntropyStepDisplacement_le_bregmanCorrection
        (n := n) hn h_traj hx0 k
    have hgap_mul :
        t k * ((f (x k)).toReal - fOpt) ≤
          t k * inner ℝ (g k) (x k - xStar) := by
      exact mul_le_mul_of_nonneg_left hgap (le_of_lt (h_traj.stepsize_pos k))
    have hsplit :
        t k * inner ℝ (g k) (x k - xStar) =
          t k * inner ℝ (g k) (x (k + 1) - xStar) +
            t k * inner ℝ (g k) (x k - x (k + 1)) := by
      -- Split the step pairing into the forward comparison term and the step displacement term.
      have hdecomp : x k - xStar = (x (k + 1) - xStar) + (x k - x (k + 1)) := by
        abel
      rw [hdecomp, inner_add_right]
      ring
    -- Combine the optimality-gap pairing bound with the forward Bregman drop and the correction.
    calc
      t k * ((f (x k)).toReal - fOpt) ≤ t k * inner ℝ (g k) (x k - xStar) := hgap_mul
      _ =
          t k * inner ℝ (g k) (x (k + 1) - xStar) +
            t k * inner ℝ (g k) (x k - x (k + 1)) := hsplit
      _ ≤
          (B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1)) - B[ωₑ] (x (k + 1)) (x k)) +
            (B[ωₑ] (x (k + 1)) (x k) +
              ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2) := by
                exact add_le_add hforward hdisplacement
      _ =
          B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1)) +
            ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2 := by
              ring
  have hweighted :
      Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * ((f (x k)).toReal - fOpt)) ≤
        B[ωₑ] xStar (x 0) +
          (1 / 2 : ℝ) *
            Finset.sum (Finset.range (N + 1))
              (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) := by
    have hsum_le := Finset.sum_le_sum hpointwise
    have hsplit :
        Finset.sum (Finset.range (N + 1))
            (fun k ↦
              (B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1))) +
                ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2) =
          Finset.sum (Finset.range (N + 1))
              (fun k ↦ B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1))) +
            Finset.sum (Finset.range (N + 1))
              (fun k ↦ ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2) := by
      -- Separate the exact Bregman telescope from the realized norm-correction prefix.
      rw [Finset.sum_add_distrib]
    have htele :
        Finset.sum (Finset.range (N + 1))
            (fun k ↦ B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1))) =
          B[ωₑ] xStar (x 0) - B[ωₑ] xStar (x (N + 1)) := by
      -- The Bregman-drop prefix is an exact finite telescope.
      exact simplexBregmanDifference_sum_range (x := x) xStar N
    have htail_nonneg :
        0 ≤ B[ωₑ] xStar (x (N + 1)) := by
      have hxN_simplex : x (N + 1) ∈ Δ := h_traj.mem_feasible_set (N + 1)
      have hxN_pos := simplexMirrorDescentIterate_pos (n := n) hn h_traj hx0 (N + 1)
      have hhalf_le :
          (1 / 2 : ℝ) * ‖toLp 1 (fun i ↦ xStar i - x (N + 1) i)‖ ^ (2 : ℕ) ≤
            B[ωₑ] xStar (x (N + 1)) := by
        simpa using
          negativeEntropyBregman_ge_halfL1Sq_of_memSimplex
            (n := n) hxStar_data.1 hxN_simplex hxN_pos
      have hhalf_nonneg :
          0 ≤ (1 / 2 : ℝ) * ‖toLp 1 (fun i ↦ xStar i - x (N + 1) i)‖ ^ (2 : ℕ) := by
        have hnorm_nonneg : 0 ≤ ‖toLp 1 (fun i ↦ xStar i - x (N + 1) i)‖ := norm_nonneg _
        nlinarith
      linarith
    calc
      Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * ((f (x k)).toReal - fOpt))
        ≤ Finset.sum (Finset.range (N + 1))
            (fun k ↦
              (B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1))) +
                ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2) := hsum_le
      _ =
          Finset.sum (Finset.range (N + 1))
              (fun k ↦ B[ωₑ] xStar (x k) - B[ωₑ] xStar (x (k + 1))) +
            Finset.sum (Finset.range (N + 1))
              (fun k ↦ ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2) := hsplit
      _ =
          (B[ωₑ] xStar (x 0) - B[ωₑ] xStar (x (N + 1))) +
            Finset.sum (Finset.range (N + 1))
              (fun k ↦ ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2) := by
            rw [htele]
      _ ≤
          B[ωₑ] xStar (x 0) +
            Finset.sum (Finset.range (N + 1))
              (fun k ↦ ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2) := by
            linarith
      _ =
          B[ωₑ] xStar (x 0) +
            (1 / 2 : ℝ) *
              Finset.sum (Finset.range (N + 1))
                (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) := by
            have hcorr :
                Finset.sum (Finset.range (N + 1))
                    (fun k ↦ ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2) =
                  (1 / 2 : ℝ) *
                    Finset.sum (Finset.range (N + 1))
                      (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) := by
              calc
                Finset.sum (Finset.range (N + 1))
                    (fun k ↦ ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) / 2)
                    =
                      Finset.sum (Finset.range (N + 1))
                        (fun k ↦
                          (1 / 2 : ℝ) *
                            ((t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ))) := by
                              refine Finset.sum_congr rfl ?_
                              intro k hk
                              ring
                _ =
                    (1 / 2 : ℝ) *
                      Finset.sum (Finset.range (N + 1))
                        (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) := by
                          rw [Finset.mul_sum]
            rw [hcorr]
  have hprefix_pos :
      0 < Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) :=
    simplexPositiveStepsizePrefixSum_pos (n := n) h_traj N
  have hbest_weighted :
      (Finset.sum (Finset.range (N + 1)) (fun k ↦ t k)) *
          (best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt) ≤
        Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * ((f (x k)).toReal - fOpt)) := by
    calc
      (Finset.sum (Finset.range (N + 1)) (fun k ↦ t k)) *
          (best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt)
        =
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ t k * (best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt)) := by
              rw [Finset.sum_mul]
      _ ≤ Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * ((f (x k)).toReal - fOpt)) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            have hbest_le :
                best_achieved_function_value (fun y ↦ (f y).toReal) x N ≤
                  (f (x k)).toReal :=
              best_achieved_function_value_le_objective_value
                (fun y ↦ (f y).toReal) x N k hk
            exact
              mul_le_mul_of_nonneg_left
                (sub_le_sub_right hbest_le fOpt)
                (le_of_lt (h_traj.stepsize_pos k))
  have hmain :
      (Finset.sum (Finset.range (N + 1)) (fun k ↦ t k)) *
          (best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt) ≤
        B[ωₑ] xStar (x 0) +
          (1 / 2 : ℝ) *
            Finset.sum (Finset.range (N + 1))
              (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) := by
    exact hbest_weighted.trans hweighted
  -- Divide by the strictly positive stepsize prefix sum to isolate the running-best gap.
  rw [le_div_iff₀ hprefix_pos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmain

-- Proof sketch: this is the simplex specialization of the mirror-descent fixed-horizon estimate,
-- with the feasible set `Δ_n`, mirror map the simplex negative entropy, initialization
-- `x⁰ = (1 / n)e`, entropy diameter `Θ₀ = log n`, and the source norm bound
-- `‖g_k‖_∞ ≤ L_{f,∞}` encoded by `‖toLp ⊤ (g k)‖ ≤ LfInf`.
-- The required optimizer witness is chosen internally from `h_problem.optimal_set_nonempty`.
/-- Text 9.9: the simplex negative-entropy mirror-descent estimate before optimizing the constant
stepsize. If the chosen simplex mirror-descent trajectory starts at `x⁰ = (1 / n)e` and its
selected subgradients satisfy `‖g_k‖_∞ ≤ L_{f,∞}` on the first `N + 1` iterations, then the
running-best objective value gap is bounded by the fixed-iteration mirror-descent objective with
`Θ₀ = log n` and `σ = 1`. -/
theorem simplex_negative_entropy_best_value_gap_le_fixed_iteration_objective
    (hn : 0 < n) {f : E → EReal} {XStar : Set E} {fOpt LfInf : ℝ}
    (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
    {x g : ℕ → E} {t : ℕ → ℝ}
    (h_traj :
      is_mirror_descent_trajectory
        (fun y ↦ (f y).toReal)
        (fun y ↦ (negative_entropy_function n y).toReal)
        Δ
        x
        g
        t)
    (hx0 : x 0 = (uniform_simplex_point hn : E))
    {N : ℕ}
    (h_subgrad_bound :
      ∀ k : Fin (N + 1), ‖toLp ⊤ (fun i ↦ g k i)‖ ≤ LfInf) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      fixed_iteration_objective
        (Real.log (n : ℝ))
        (LfInf ^ 2 / 2)
        (fun k : Fin (N + 1) ↦ t k) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  have hxStar_data : xStar ∈ Δ ∧ IsMinOn f Δ xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hprefix :=
    simplexNegativeEntropyBestGapLeWithNormCorrection
      (n := n) (hn := hn) (h_problem := h_problem)
      (h_traj := h_traj) (hx0 := hx0) hxStar N
  have hsum_pos :
      0 < Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) :=
    simplexPositiveStepsizePrefixSum_pos (n := n) h_traj N
  have hdiam :
      B[ωₑ] xStar (x 0) ≤ Real.log (n : ℝ) := by
    -- The simplex entropy diameter at the uniform initialization is exactly `log n`.
    rw [hx0]
    exact negative_entropy_bregman_le_log_of_mem_simplex hn hxStar_data.1
  have hcorr_sum_le :
      Finset.sum (Finset.range (N + 1))
          (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) ≤
        Finset.sum (Finset.range (N + 1))
          (fun k ↦ (t k) ^ (2 : ℕ) * LfInf ^ (2 : ℕ)) := by
    -- Dominate each realized `ℓ_∞` correction by the prescribed prefix bound `LfInf²`.
    refine Finset.sum_le_sum ?_
    intro k hk
    have hk_bound : ‖toLp ⊤ (fun i ↦ g k i)‖ ≤ LfInf := by
      exact h_subgrad_bound ⟨k, by simpa using hk⟩
    have hsq_le : ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ) ≤ LfInf ^ (2 : ℕ) := by
      have hnorm_nonneg : 0 ≤ ‖toLp ⊤ (fun i ↦ g k i)‖ := norm_nonneg _
      have hLfInf_nonneg : 0 ≤ LfInf := le_trans hnorm_nonneg hk_bound
      nlinarith
    exact mul_le_mul_of_nonneg_left hsq_le (sq_nonneg (t k))
  have hcorr_le :
      (1 / 2 : ℝ) *
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) ≤
        (LfInf ^ 2 / 2) *
          Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ)) := by
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    calc
      (1 / 2 : ℝ) *
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ))
        ≤
          (1 / 2 : ℝ) *
            Finset.sum (Finset.range (N + 1))
              (fun k ↦ (t k) ^ (2 : ℕ) * LfInf ^ (2 : ℕ)) := by
                exact mul_le_mul_of_nonneg_left hcorr_sum_le hhalf_nonneg
      _ =
          (1 / 2 : ℝ) *
            (Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ)) * LfInf ^ (2 : ℕ)) := by
              rw [Finset.sum_mul]
      _ =
          (LfInf ^ 2 / 2) *
            Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ)) := by
              ring
  have hnum_le :
      B[ωₑ] xStar (x 0) +
          (1 / 2 : ℝ) *
            Finset.sum (Finset.range (N + 1))
              (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ)) ≤
        Real.log (n : ℝ) +
          (LfInf ^ 2 / 2) *
            Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ)) := by
    exact add_le_add hdiam hcorr_le
  have hobjective :
      (Real.log (n : ℝ) +
          (LfInf ^ 2 / 2) *
            Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ))) /
        Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) =
      fixed_iteration_objective
        (Real.log (n : ℝ))
        (LfInf ^ 2 / 2)
        (fun k : Fin (N + 1) ↦ t k) := by
    have hsq :
        (∑ k : Fin (N + 1), t k ^ (2 : ℕ)) =
          Finset.sum (Finset.range (N + 1)) (fun k ↦ t k ^ (2 : ℕ)) := by
      simpa using (Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ t k ^ (2 : ℕ)) (N + 1))
    have hsum :
        (∑ k : Fin (N + 1), t k) =
          Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
      simpa using (Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ t k) (N + 1))
    rw [fixed_iteration_objective, hsq, hsum]
  -- Route correction: first prove the exact prefix ratio with the realized `ℓ_∞` correction,
  -- then replace that correction by the textbook bound `LfInf²`.
  calc
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt
        ≤
          (B[ωₑ] xStar (x 0) +
              (1 / 2 : ℝ) *
                Finset.sum (Finset.range (N + 1))
                  (fun k ↦ (t k) ^ (2 : ℕ) * ‖toLp ⊤ (fun i ↦ g k i)‖ ^ (2 : ℕ))) /
            Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := hprefix
    _ ≤
        (Real.log (n : ℝ) +
            (LfInf ^ 2 / 2) *
              Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ))) /
          Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
            exact div_le_div_of_nonneg_right hnum_le hsum_pos.le
    _ =
        fixed_iteration_objective
          (Real.log (n : ℝ))
          (LfInf ^ 2 / 2)
          (fun k : Fin (N + 1) ↦ t k) := hobjective

-- Proof sketch: combine
-- `simplex_negative_entropy_best_value_gap_le_fixed_iteration_objective` with the constant-step
-- specialization `t_k = √(2 log n) / (L_{f,∞} √(N + 1))`, using Text 9.7 only as the internal
-- bridge back to the core owner `fixed_iteration_uniform_steps`. The optimizer witness is chosen
-- internally from `h_problem.optimal_set_nonempty`. The assumption `1 < n` gives `0 < log n`,
-- and positivity of `L_{f,∞}` is carried by `PosReal`.
-- Simplifying the fixed-iteration value then yields the owner definition
-- `simplex_non_euclidean_upper_bound`.
/-- Consequence of Text 9.9 (1): for mirror descent on the unit simplex `Δ_n` with the `ℓ_1`
norm, negative entropy mirror map, uniform initialization `x⁰ = (1 / n)e`, and positive
sup-norm Lipschitz constant `L_{f,∞}`, the optimal constant stepsizes from Text 9.7 give the
running-best objective value gap bound `√(2 log n) L_{f,∞} / √(N + 1)` when `1 < n`. -/
theorem simplex_negative_entropy_best_value_gap_le_non_euclidean_upper_bound
    {f : E → EReal} {XStar : Set E} {fOpt : ℝ} {LfInf : PosReal}
    (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
    {x g : ℕ → E} {t : ℕ → ℝ}
    (h_traj :
      is_mirror_descent_trajectory
        (fun y ↦ (f y).toReal)
        (fun y ↦ (negative_entropy_function n y).toReal)
        Δ
        x
        g
        t)
    {N : ℕ}
    (h_subgrad_bound :
      ∀ k : Fin (N + 1), ‖toLp ⊤ (fun i ↦ g k i)‖ ≤ (LfInf : ℝ))
    (hn : 1 < n)
    (hx0 : x 0 = (uniform_simplex_point (Nat.zero_lt_of_lt hn) : E))
    (h_stepsize :
      ∀ k : Fin (N + 1),
        t k =
          Real.sqrt (2 * Real.log (n : ℝ)) /
            ((LfInf : ℝ) * Real.sqrt (N + 1 : ℝ))) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      simplex_non_euclidean_upper_bound n LfInf N := by
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    have hn_real : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    exact Real.log_pos hn_real
  have hsteps_eq :
      (fun k : Fin (N + 1) ↦ t k) =
        mirror_descent_textbook_stepsize (Real.log (n : ℝ)) (LfInf : ℝ) 1 N := by
    funext k
    rw [mirror_descent_textbook_stepsize_apply]
    simpa using h_stepsize k
  have hfixed :=
    simplex_negative_entropy_best_value_gap_le_fixed_iteration_objective
      (n := n) (hn := Nat.zero_lt_of_lt hn)
      (h_problem := h_problem) (h_traj := h_traj) (hx0 := hx0)
      (N := N) (h_subgrad_bound := h_subgrad_bound)
  have hobjective :
      fixed_iteration_objective
          (Real.log (n : ℝ))
          (((LfInf : ℝ) ^ 2) / 2)
          (fun k : Fin (N + 1) ↦ t k) =
        simplex_non_euclidean_upper_bound n LfInf N := by
    have hsqrt :
        Real.sqrt (2 * Real.log (n : ℝ)) =
          Real.sqrt 2 * Real.sqrt (Real.log (n : ℝ)) := by
      rw [mul_comm, Real.sqrt_mul (le_of_lt hlog_pos), mul_comm]
    -- Route correction: rewrite the prescribed stepsizes to the Text 9.7 owner and evaluate it.
    rw [hsteps_eq]
    calc
      fixed_iteration_objective
          (Real.log (n : ℝ))
          (((LfInf : ℝ) ^ 2) / 2)
          (mirror_descent_textbook_stepsize (Real.log (n : ℝ)) (LfInf : ℝ) 1 N)
          =
            (LfInf : ℝ) * (Real.sqrt 2 * Real.sqrt (Real.log (n : ℝ))) /
              Real.sqrt (1 * (N + 1 : ℝ)) := by
                simpa using
                  (mirror_descent_optimal_constant_stepsize_minimizes_fixed_iteration_bound
                    (Real.log (n : ℝ)) (LfInf : ℝ) 1 N hlog_pos LfInf.2 (by norm_num)).2
      _ = simplex_non_euclidean_upper_bound n LfInf N := by
            rw [simplex_non_euclidean_upper_bound, hsqrt]
            ring_nf
  calc
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt
        ≤
          fixed_iteration_objective
            (Real.log (n : ℝ))
            (((LfInf : ℝ) ^ 2) / 2)
            (fun k : Fin (N + 1) ↦ t k) := hfixed
    _ = simplex_non_euclidean_upper_bound n LfInf N := hobjective

end

-- Proof sketch: expand the three owner definitions, cancel the common factor
-- `√2 / √(N + 1)`, and simplify the quotient of the two upper bounds to
-- `√(log n) * LfInf / Lf2`.
/-- The efficiency ratio agrees with the quotient of the named non-Euclidean and Euclidean upper
bound constants. -/
theorem simplex_efficiency_ratio_eq_upper_bound_ratio
    (n : ℕ) (LfInf Lf2 : PosReal) (N : ℕ) :
    simplex_efficiency_ratio n LfInf Lf2 =
      simplex_non_euclidean_upper_bound n LfInf N /
        simplex_euclidean_upper_bound Lf2 N := by
  by_cases hlog : 0 ≤ Real.log (n : ℝ)
  · have hsqrt :
        Real.sqrt (2 * Real.log (n : ℝ)) =
          Real.sqrt 2 * Real.sqrt (Real.log (n : ℝ)) := by
      rw [mul_comm, Real.sqrt_mul hlog, mul_comm]
    have hsqrtN_ne : Real.sqrt (N + 1 : ℝ) ≠ 0 := by
      positivity
    have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
      positivity
    have hLf2_ne : (Lf2 : ℝ) ≠ 0 := ne_of_gt Lf2.2
    -- Expand the three named constants and cancel the common positive factors.
    unfold simplex_efficiency_ratio simplex_non_euclidean_upper_bound simplex_euclidean_upper_bound
    rw [hsqrt]
    field_simp [hsqrtN_ne, hsqrt2_ne, hLf2_ne]
  · have hlog_nonpos : Real.log (n : ℝ) ≤ 0 := le_of_not_ge hlog
    have htwo_log_nonpos : 2 * Real.log (n : ℝ) ≤ 0 := by
      nlinarith
    -- If `log n ≤ 0`, both square-root numerators vanish and the identity is immediate.
    unfold simplex_efficiency_ratio simplex_non_euclidean_upper_bound simplex_euclidean_upper_bound
    simp [Real.sqrt_eq_zero_of_nonpos hlog_nonpos,
      Real.sqrt_eq_zero_of_nonpos htwo_log_nonpos]

-- Proof sketch: rewrite the ratio using `simplex_efficiency_ratio_eq_upper_bound_ratio` and the
-- explicit formula `ρ = √(log n) * (L_{f,∞} / L_{f,2})`.
-- Then apply the standard norm-comparison consequences
-- `L_{f,∞} ≤ L_{f,2} ≤ √n L_{f,∞}` to bound the quotient `L_{f,∞} / L_{f,2}` between
-- `1 / √n` and `1`.
/-- Comparison consequence for Text 9.9 (2): if the Euclidean and sup-norm Lipschitz constants
satisfy `L_{f,∞} ≤ L_{f,2} ≤ √n L_{f,∞}`, then the comparison ratio of the non-Euclidean and
Euclidean upper bounds lies between `√(log n) / √n` and `√(log n)`. -/
theorem simplex_efficiency_ratio_bounds
    (n : ℕ) (LfInf Lf2 : PosReal)
    (h_upper : (LfInf : ℝ) ≤ (Lf2 : ℝ))
    (h_lower : (Lf2 : ℝ) ≤ Real.sqrt (n : ℝ) * (LfInf : ℝ)) :
    Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) ≤
      simplex_efficiency_ratio n LfInf Lf2 ∧
      simplex_efficiency_ratio n LfInf Lf2 ≤ Real.sqrt (Real.log (n : ℝ)) := by
  by_cases hlog : 0 ≤ Real.log (n : ℝ)
  · have hsqrt_log_nonneg : 0 ≤ Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_nonneg _
    have hLf2_pos : 0 < (Lf2 : ℝ) := Lf2.2
    have hLfInf_pos : 0 < (LfInf : ℝ) := LfInf.2
    have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
      by_contra hsqrt_n_not_pos
      have hsqrt_n_nonpos : Real.sqrt (n : ℝ) ≤ 0 := le_of_not_gt hsqrt_n_not_pos
      have hsqrt_n_eq_zero : Real.sqrt (n : ℝ) = 0 := by
        exact le_antisymm hsqrt_n_nonpos (Real.sqrt_nonneg _)
      have hLf2_nonpos : (Lf2 : ℝ) ≤ 0 := by
        simpa [hsqrt_n_eq_zero] using h_lower
      exact not_le_of_gt hLf2_pos hLf2_nonpos
    have hsqrt_n_ne : Real.sqrt (n : ℝ) ≠ 0 := hsqrt_n_pos.ne'
    have hLf2_ne : (Lf2 : ℝ) ≠ 0 := ne_of_gt hLf2_pos
    have hratio_lower :
        (1 : ℝ) / Real.sqrt (n : ℝ) ≤ (LfInf : ℝ) / Lf2 := by
      field_simp [hsqrt_n_ne, hLf2_ne]
      nlinarith [h_lower]
    have hratio_upper : (LfInf : ℝ) / Lf2 ≤ 1 := by
      field_simp [hLf2_ne]
      nlinarith [h_upper]
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hratio_lower hsqrt_log_nonneg
      simpa [simplex_efficiency_ratio, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using hmul
    · have hmul := mul_le_mul_of_nonneg_left hratio_upper hsqrt_log_nonneg
      simpa [simplex_efficiency_ratio, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using hmul
  · have hlog_nonpos : Real.log (n : ℝ) ≤ 0 := le_of_not_ge hlog
    have hsqrt_log : Real.sqrt (Real.log (n : ℝ)) = 0 := by
      exact Real.sqrt_eq_zero_of_nonpos hlog_nonpos
    -- When `log n ≤ 0`, both comparison bounds collapse to the zero value of the ratio.
    constructor <;> simp [simplex_efficiency_ratio, hsqrt_log]
