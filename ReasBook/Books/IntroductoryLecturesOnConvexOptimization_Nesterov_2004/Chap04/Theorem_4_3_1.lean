/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Corollary_4_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Assumption_4_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient
open scoped CoordinateSubspace
open scoped ConstrainedArgmin

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 4.3.1 lies in the second-order oracle / lower-complexity domain on `ℝ^n`.

Sampled owner-style declarations:
* `IsSecondOrderSpanSequence` in `Assumption_4_3_1`, the chapter owner for the second-order
  affine-span restriction;
* `bestFunctionValueUpTo` in `Chap03/Definition_3_55`, the chapter owner for the best sampled
  objective value on a finite prefix;
* `HasLipschitzContinuousHessian` and the notation `C22[L]` in `Definition_4_2_7`, the chapter
  owner for globally Hessian-Lipschitz objectives;
* the project-standard positive-parameter owner `NNRealˣ`, used throughout the project whenever a
  displayed denominator is mathematically required to stay strictly positive;
* `SatisfiesSpanCondition` in `Chap02/Definition_2_9`, the earlier chapter pattern showing that a
  lower-complexity method should be modeled by its primitive iterate family, with the span
  restriction kept as a separate theorem-level hypothesis rather than as bundled data.

Source/core/bridge triage:
* source-facing: the cubic hard-instance lower bound for a second-order method complexity profile;
* core/canonical: `IsSecondOrderSpanSequence`, `bestFunctionValueUpTo`, and `f ∈ C22[L]`;
* bridge/view: the trajectory-value specialization `fun i ↦ f (testPoints f x0 i)` of the owner
  sampled-minimum API.

Primitive data:
* the iterate family `testPoints`;
* the strictly positive complexity profile `complexityConstant`.

Derived API:
* the initialization law `testPoints f x0 0 = x0`;
* the second-order span restriction on every `C²` objective;
* the uniform guarantee on `bestFunctionValueUpTo` for every Hessian-Lipschitz objective.

The previous file bundled the theorem hypotheses into a local `SecondOrderMethod` structure and
redefined the sampled-prefix minimum locally. The refinement keeps the source-facing theorem, but
uses the chapter owners `IsSecondOrderSpanSequence`, `bestFunctionValueUpTo`, and `C22[L]`
directly, leaving only the genuine primitive data as explicit inputs. The complexity denominator is
owned by `NNRealˣ`, so the displayed quantity `L_f ρ₀^3 / C_𝓜(k)` keeps its textbook
positive-denominator semantics instead of degenerating at `C_𝓜(k) = 0`.
-/

/-- Helper for Theorem 4.3.1: the hard-instance second-order span sequence reaches only the first
`i` coordinates after `i` oracle calls. -/
private theorem hard_instance_iterates_mem_coordinateSubspace
    {t : ℕ} (htn : t ≤ n) {seq : ℕ → E}
    (hseq : IsSecondOrderSpanSequence (fk htn) seq)
    (hzero : seq 0 = 0) :
    ∀ {s : ℕ}, s ≤ t → ∀ {i : ℕ}, i ≤ s → seq i ∈ ℝ^{i,n} := by
  intro s
  induction s with
  | zero =>
      intro hs i hi
      have hi0 : i = 0 := by omega
      subst hi0
      -- The zero initialization lies in every coordinate-zero tail at level `0`.
      rw [hzero, mem_coordinateSubspace_iff]
      intro j hj
      simp
  | succ s ih =>
      intro hs i hi
      by_cases his : i ≤ s
      · -- Earlier iterates stay in their own coordinate subspaces by the induction hypothesis.
        exact ih (by omega) his
      · have his_eq : i = s + 1 := by omega
        subst his_eq
        have hprefix : ∀ j : Fin (s + 1), seq j ∈ ℝ^{j,n} := by
          intro j
          simpa using ih (by omega) (show (j : ℕ) ≤ s by omega)
        -- The source-faithful next-iterate corollary propagates the support bound one step.
        exact
          fk_spanSequence_next_iterate_mem_coordinateSubspace
            (k := s) (t := t) (by omega) htn hseq hprefix

/-- Helper for Theorem 4.3.1: Proposition 4.3.1 turns the minimizer distance bound into the
radius parameter used in the complexity guarantee. -/
private theorem hard_instance_radius_le_sqrt_bound
    {t : ℕ} (htn : t ≤ n) :
    ‖(0 : E) - cubicLowerBoundMinimizer n t‖ ≤
      Real.sqrt ((((t + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3) := by
  let b : ℝ := (((t + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hsq : ‖(0 : E) - cubicLowerBoundMinimizer n t‖ ^ (2 : ℕ) ≤ b := by
    exact le_of_lt (by simpa [b] using cubicLowerBoundMinimizer_sqDist_lt (n := n) htn)
  have hsq' :
      ‖(0 : E) - cubicLowerBoundMinimizer n t‖ ^ (2 : ℕ) ≤ (Real.sqrt b) ^ (2 : ℕ) := by
    simpa [Real.sq_sqrt hb_nonneg] using hsq
  exact
    (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 <|
      by simpa [b] using hsq'

/-- Helper for Theorem 4.3.1: after rewriting `t = (3m + 2) + (m + 1)`, the hard instances
`f_t` and `f_{3m+2}` agree on `ℝ^{3m+2,n}`. -/
private theorem hard_instance_prefixValueEq
    {m t : ℕ} (ht : t = (3 * m + 2) + (m + 1)) (htn : t ≤ n)
    {x : E} (hx : x ∈ ℝ^{3 * m + 2,n}) :
    fk htn x = fk (show 3 * m + 2 ≤ n by omega) x := by
  subst ht
  have hsmall :
      fk (le_trans (Nat.le_add_right (3 * m + 2) (m + 1)) htn) x =
        fk (show 3 * m + 2 ≤ n by omega) x := by
    -- Proof irrelevance identifies the smaller hard-instance proof argument.
    exact congrArg (fun h : 3 * m + 2 ≤ n ↦ fk h x) (Subsingleton.elim _ _)
  -- Route correction: first align the hard-instance index as `k + p`, then remove the zero tail.
  calc
    fk htn x = fk (le_trans (Nat.le_add_right (3 * m + 2) (m + 1)) htn) x := by
      simpa using
        (fk_add_eq_of_mem_coordinateSubspace
          (k := 3 * m + 2) (p := m + 1) htn hx)
    _ = fk (show 3 * m + 2 ≤ n by omega) x := hsmall

/-- Helper for Theorem 4.3.1: the optimal-value gap between `f_{3m+2}` and `f_{4m+3}` is exactly
`(2 / 3) (m + 1)`. -/
private theorem hard_instance_minimizerGapEq
    {m t : ℕ} (ht : t = 4 * m + 3) (htn : t ≤ n) :
    ((2 : ℝ) / 3) * (m + 1) =
      fk (show 3 * m + 2 ≤ n by omega) (cubicLowerBoundMinimizer n (3 * m + 2)) -
        fk htn (cubicLowerBoundMinimizer n t) := by
  have hkn : 3 * m + 2 ≤ n := by
    omega
  -- Rewrite both minimizer values by the closed-form formula before normalizing casts.
  rw [cubicLowerBoundObjective_value_at_minimizer (n := n) hkn,
    cubicLowerBoundObjective_value_at_minimizer (n := n) htn]
  subst t
  norm_num
  ring_nf

/-- Helper for Theorem 4.3.1: the raw hard-instance upper bound is bounded by the textbook
quantity `36 (k + 1)^3 √(k + 1)` when `k = 3m + 2`. -/
private theorem hard_instance_rhs_le_textbookBound
    {m t : ℕ} (ht : t = 4 * m + 3) :
    (8 * Real.sqrt 2) *
        (Real.sqrt ((((t + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3)) ^ 3 /
        (((2 : ℝ) / 3) * (m + 1)) ≤
      36 * ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ) ^ 3 *
        Real.sqrt ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ))) := by
  subst t
  let s : ℝ := (m + 1 : ℕ)
  have hs : ((m + 1 : ℕ) : ℝ) = s := rfl
  have hs_pos : 0 < s := by
    -- The block length `m + 1` is strictly positive.
    dsimp [s]
    exact_mod_cast Nat.succ_pos m
  have hs_nonneg : 0 ≤ s := hs_pos.le
  have hs_div_nonneg : 0 ≤ s / 3 := by
    positivity
  have hsqrt_raw :
      Real.sqrt ((((4 * m + 3 + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3) =
        8 * s * Real.sqrt (s / 3) := by
    have hs_four : (((4 * m + 3 + 1 : ℕ) : ℝ)) = 4 * s := by
      dsimp [s]
      norm_num
      ring
    -- Isolate the perfect square factor `(8s)^2` before taking the square root.
    calc
      Real.sqrt ((((4 * m + 3 + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3)
          = Real.sqrt (((8 * s) ^ (2 : ℕ)) * (s / 3)) := by
              rw [hs_four]
              ring_nf
      _ = Real.sqrt ((8 * s) ^ (2 : ℕ)) * Real.sqrt (s / 3) := by
            rw [Real.sqrt_mul]
            positivity
      _ = 8 * s * Real.sqrt (s / 3) := by
            have h8s_nonneg : 0 ≤ 8 * s := by
              exact mul_nonneg (by positivity) hs_nonneg
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h8s_nonneg]
  have hsqrt_rhs :
      Real.sqrt ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ)) =
        3 * Real.sqrt (s / 3) := by
    have hs_three : ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ)) = 3 * s := by
      dsimp [s]
      norm_num
      ring
    -- Rewrite `3s` as `3^2 * (s / 3)` so the square root pulls out a factor of `3`.
    calc
      Real.sqrt ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ))
          = Real.sqrt (((3 : ℝ) ^ (2 : ℕ)) * (s / 3)) := by
              rw [hs_three]
              ring_nf
      _ = Real.sqrt ((3 : ℝ) ^ (2 : ℕ)) * Real.sqrt (s / 3) := by
            rw [Real.sqrt_mul]
            positivity
      _ = 3 * Real.sqrt (s / 3) := by
            norm_num
  have hsqrt_div_cube :
      (Real.sqrt (s / 3)) ^ (3 : ℕ) = (s / 3) * Real.sqrt (s / 3) := by
    -- Replace the square inside the cube by the radicand itself.
    have hsq : Real.sqrt (s / 3) * Real.sqrt (s / 3) = s / 3 := by
      nlinarith [Real.sq_sqrt hs_div_nonneg]
    calc
      (Real.sqrt (s / 3)) ^ (3 : ℕ)
          = (Real.sqrt (s / 3) * Real.sqrt (s / 3)) * Real.sqrt (s / 3) := by
              ring
      _ = (s / 3) * Real.sqrt (s / 3) := by
            rw [hsq]
  have hraw_eq :
      (8 * Real.sqrt 2) *
          (Real.sqrt ((((4 * m + 3 + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3)) ^ 3 /
          (((2 : ℝ) / 3) * (m + 1)) =
        (2048 * Real.sqrt 2) * (s ^ 3 * Real.sqrt (s / 3)) := by
    have hden_eq : (((2 : ℝ) / 3) * (m + 1)) = ((2 : ℝ) / 3) * s := by
      dsimp [s]
      norm_num
    rw [hsqrt_raw, hden_eq]
    rw [show (8 * s * Real.sqrt (s / 3)) = (8 * s) * Real.sqrt (s / 3) by ring]
    rw [mul_pow, hsqrt_div_cube]
    field_simp [hs_pos.ne']
    ring_nf
  have hrhs_eq :
      36 * ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ) ^ 3 *
          Real.sqrt ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ))) =
        2916 * (s ^ 3 * Real.sqrt (s / 3)) := by
    have hs_three : ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ)) = 3 * s := by
      dsimp [s]
      norm_num
      ring
    have hsqrt_three : Real.sqrt (3 * s) = 3 * Real.sqrt (s / 3) := by
      calc
        Real.sqrt (3 * s) = Real.sqrt ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ)) := by
          rw [← hs_three]
        _ = 3 * Real.sqrt (s / 3) := hsqrt_rhs
    rw [hs_three, hsqrt_three]
    ring_nf
  rw [hraw_eq, hrhs_eq]
  have hfactor_nonneg : 0 ≤ s ^ 3 * Real.sqrt (s / 3) := by
    positivity
  have hsqrt_two_sq : (Real.sqrt 2 : ℝ) ^ (2 : ℕ) = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hconst_sq : (2048 * Real.sqrt 2 : ℝ) ^ (2 : ℕ) ≤ (2916 : ℝ) ^ (2 : ℕ) := by
    nlinarith [hsqrt_two_sq]
  refine mul_le_mul_of_nonneg_right ?_ hfactor_nonneg
  exact
    (sq_le_sq₀ (by positivity : 0 ≤ (2048 * Real.sqrt 2 : ℝ))
      (by positivity : 0 ≤ (2916 : ℝ))).1 hconst_sq

/-- Helper for Theorem 4.3.1: on the first `3m + 3` sampled points, the hard instance
`f_{4m+3}` agrees with `f_{3m+2}` on the reachable coordinate subspace, so the sampled gap is at
least the explicit optimum gap between those two hard instances. -/
private theorem hard_instance_sampled_gap_lower_bound
    {m t : ℕ} (ht : t = 4 * m + 3) (htn : t ≤ n)
    {seq : ℕ → E}
    (hiterates : ∀ i : Fin ((3 * m + 2) + 1), seq i ∈ ℝ^{i,n}) :
    ((2 : ℝ) / 3) * (m + 1) ≤
      bestFunctionValueUpTo (fun i ↦ fk htn (seq i)) (3 * m + 2) -
        fk htn (cubicLowerBoundMinimizer n t) := by
  have hkn : 3 * m + 2 ≤ n := by
    omega
  have htp : t = (3 * m + 2) + (m + 1) := by
    omega
  have hmin_mem :
      cubicLowerBoundMinimizer n (3 * m + 2) ∈ argmin[Set.univ] (fk hkn) := by
    simpa [cubicLowerBoundObjective_argmin_eq_singleton (n := n) hkn]
  have hmin :
      IsMinOn (fk hkn) Set.univ (cubicLowerBoundMinimizer n (3 * m + 2)) :=
    (mem_constrainedArgmin_iff.mp hmin_mem).2
  rw [isMinOn_iff] at hmin
  have hbest_lower :
      fk hkn (cubicLowerBoundMinimizer n (3 * m + 2)) ≤
        bestFunctionValueUpTo (fun i ↦ fk htn (seq i)) (3 * m + 2) := by
    refine le_ciInf ?_
    intro i
    have hcoord :
        seq i ∈ ℝ^{3 * m + 2,n} :=
      mem_coordinateSubspace_mono (show (i : ℕ) ≤ 3 * m + 2 by omega) (hiterates i)
    have hvalue_eq : fk htn (seq i) = fk hkn (seq i) := by
      -- Route correction: rewrite `t` as `(3m + 2) + (m + 1)` before dropping the zero tail.
      simpa using hard_instance_prefixValueEq (n := n) (m := m) htp htn hcoord
    calc
      fk hkn (cubicLowerBoundMinimizer n (3 * m + 2)) ≤ fk hkn (seq i) := by
        exact hmin (seq i) (by simp)
      _ = fk htn (seq i) := hvalue_eq.symm
  have hvalue_gap :
      ((2 : ℝ) / 3) * (m + 1) =
        fk hkn (cubicLowerBoundMinimizer n (3 * m + 2)) -
          fk htn (cubicLowerBoundMinimizer n t) := by
    -- The two minimizer values are explicit, so only a casted polynomial identity remains.
    simpa using hard_instance_minimizerGapEq (n := n) (m := m) ht htn
  calc
    ((2 : ℝ) / 3) * (m + 1) =
        fk hkn (cubicLowerBoundMinimizer n (3 * m + 2)) -
          fk htn (cubicLowerBoundMinimizer n t) := hvalue_gap
    _ ≤ bestFunctionValueUpTo (fun i ↦ fk htn (seq i)) (3 * m + 2) -
          fk htn (cubicLowerBoundMinimizer n t) := by
        exact sub_le_sub_right hbest_lower _

-- Proof sketch: apply the hard-instance family `f_t` with `t = 4m + 3` and start from `x₀ = 0`.
-- The span-sequence restriction keeps the first `k + 1` iterates in the coordinate subspaces
-- given by Corollary 4.3.1, so Lemma 4.3.2 identifies the best value among those iterates with
-- the hard-instance gap `f_k^* - f_t^* = (2 / 3) (m + 1)`. Proposition 4.3.2 supplies the
-- Hessian-Lipschitz constant on the canonical `C22[...]` surface, Proposition 4.3.1 controls the
-- distance from `0` to the minimizer, and rearranging the assumed estimate (4.3.7) yields the
-- displayed upper bound.
/-- Theorem 4.3.1: let the Hessian of the objective be Lipschitz continuous with constant `L_f`,
and let a second-order method satisfy the textbook second-order information restriction and the
guarantee
`min_{0 ≤ i ≤ k} f(x_i) - f(x^*) ≤ L_f ρ₀^3 / C_𝓜(k)` for every starting point
`x₀` with `‖x₀ - x^*‖ ≤ ρ₀`. Then, whenever `k = 3m + 2` with `m + 1 ≤ n / 4`
(equivalently `4 * (m + 1) ≤ n`), the strictly positive complexity quantity satisfies
`C_𝓜(k) ≤ 36 (k + 1)^{3.5}`. -/
theorem secondOrderMethod_complexityConstant_le_cubicHardInstance_bound
    (testPoints : (E → ℝ) → E → ℕ → E)
    (complexityConstant : ℕ → NNRealˣ)
    (htestPoints_zero :
      ∀ (f : E → ℝ) (x0 : E), testPoints f x0 0 = x0)
    (hspan :
      ∀ (f : E → ℝ) (_ : ContDiff ℝ 2 f) (x0 : E),
        IsSecondOrderSpanSequence f (testPoints f x0))
    (hguarantee :
      ∀ (f : E → ℝ) (Lf : NNReal) (_ : f ∈ C22[Lf])
        (xStar x0 : E) (rho0 : ℝ) (k : ℕ),
        IsMinOn f Set.univ xStar →
          ‖x0 - xStar‖ ≤ rho0 →
            bestFunctionValueUpTo (fun i ↦ f (testPoints f x0 i)) k - f xStar ≤
              (Lf : ℝ) * rho0 ^ 3 / (complexityConstant k : ℝ))
    {k m : ℕ} (hk : k = 3 * m + 2) (hm : m + 1 ≤ n / 4) :
    (complexityConstant k : ℝ) ≤
      36 * ((k + 1 : ℝ) ^ 3 * Real.sqrt (k + 1)) := by
  subst k
  let t : ℕ := 4 * m + 3
  have htn : t ≤ n := by
    dsimp [t]
    omega
  let seq : ℕ → E := testPoints (fk htn) 0
  have hseq :
      IsSecondOrderSpanSequence (fk htn) seq := by
    -- Proposition 4.3.2 supplies the `C²` regularity needed to invoke the span restriction.
    simpa [seq] using hspan (fk htn) (fk_mem_C22 (n := n) htn).contDiff (0 : E)
  have hzero : seq 0 = 0 := by
    -- The source route starts the hard instance from the zero vector.
    simpa [seq] using htestPoints_zero (fk htn) (0 : E)
  have hiterates : ∀ i : Fin ((3 * m + 2) + 1), seq i ∈ ℝ^{i,n} := by
    intro i
    -- The iterate-support invariant follows by repeatedly applying Corollary 4.3.1.
    exact
      hard_instance_iterates_mem_coordinateSubspace
        (n := n) htn hseq hzero (show 3 * m + 2 ≤ t by
          dsimp [t]
          omega) (show (i : ℕ) ≤ 3 * m + 2 by omega)
  have hgap_lower :
      ((2 : ℝ) / 3) * (m + 1) ≤
        bestFunctionValueUpTo (fun i ↦ fk htn (seq i)) (3 * m + 2) -
          fk htn (cubicLowerBoundMinimizer n t) := by
    -- The first `3m + 3` samples only explore the smaller hard instance `f_{3m+2}`.
    exact hard_instance_sampled_gap_lower_bound (n := n) (m := m) rfl htn hiterates
  have hxStar_mem :
      cubicLowerBoundMinimizer n t ∈ argmin[Set.univ] (fk htn) := by
    simpa [cubicLowerBoundObjective_argmin_eq_singleton (n := n) htn]
  have hxStar_min :
      IsMinOn (fk htn) Set.univ (cubicLowerBoundMinimizer n t) :=
    (mem_constrainedArgmin_iff.mp hxStar_mem).2
  have hradius :
      ‖(0 : E) - cubicLowerBoundMinimizer n t‖ ≤
        Real.sqrt ((((t + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3) :=
    hard_instance_radius_le_sqrt_bound (n := n) htn
  have hgap_upper :
      bestFunctionValueUpTo (fun i ↦ fk htn (seq i)) (3 * m + 2) -
        fk htn (cubicLowerBoundMinimizer n t) ≤
          (8 * Real.sqrt 2) *
            (Real.sqrt ((((t + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3)) ^ 3 /
            (complexityConstant (3 * m + 2) : ℝ) := by
    -- The assumed estimate (4.3.7) applies to the hard instance with its explicit minimizer.
    simpa [seq] using
      hguarantee
        (fk htn) ⟨8 * Real.sqrt 2, by positivity⟩ (fk_mem_C22 (n := n) htn)
        (cubicLowerBoundMinimizer n t) (0 : E)
        (Real.sqrt ((((t + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3)) (3 * m + 2)
        hxStar_min hradius
  have hcombined :
      ((2 : ℝ) / 3) * (m + 1) ≤
        (8 * Real.sqrt 2) *
          (Real.sqrt ((((t + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3)) ^ 3 /
          (complexityConstant (3 * m + 2) : ℝ) :=
    hgap_lower.trans hgap_upper
  have hraw :
      (complexityConstant (3 * m + 2) : ℝ) ≤
        (8 * Real.sqrt 2) *
          (Real.sqrt ((((t + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3)) ^ 3 /
          (((2 : ℝ) / 3) * (m + 1)) := by
    have hm_pos : (0 : ℝ) < (m + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos m
    have hdenom_pos : 0 < ((2 : ℝ) / 3) * (m + 1 : ℝ) := by
      have htwo_thirds_pos : 0 < ((2 : ℝ) / 3) := by
        norm_num
      exact mul_pos htwo_thirds_pos hm_pos
    have hmul :
        ((2 : ℝ) / 3) * (m + 1) * (complexityConstant (3 * m + 2) : ℝ) ≤
          (8 * Real.sqrt 2) *
            (Real.sqrt ((((t + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3)) ^ 3 := by
      have hcomplexity_pos : 0 < (complexityConstant (3 * m + 2) : ℝ) := by
        exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero (complexityConstant (3 * m + 2))))
      exact (le_div_iff₀ hcomplexity_pos).mp hcombined
    exact
      (le_div_iff₀ hdenom_pos).2 <|
        by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have htextbook :
      (8 * Real.sqrt 2) *
          (Real.sqrt ((((t + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3)) ^ 3 /
          (((2 : ℝ) / 3) * (m + 1)) ≤
        36 * ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ) ^ 3 *
          Real.sqrt ((((3 * m + 2 : ℕ) + 1 : ℕ) : ℝ))) := by
    -- The raw hard-instance expression collapses to a constant-factor comparison after rewriting.
    simpa [t] using hard_instance_rhs_le_textbookBound (m := m) (t := t) rfl
  simpa [Nat.cast_add] using hraw.trans htextbook

end
