/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_13
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_27
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_38
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_16
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
open scoped BigOperators

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {m : ℕ}
variable {fi : Fin m → E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable [h_problem : IsConstrainedConvexProblem (finite_sum_objective fi) C XStar fOpt]
variable (h_incremental : IncrementalProjectedSubgradientAssumptions fi C)
variable (g : ℕ → C → Fin m → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  incremental_projected_subgradient_method
    C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex t g x0 k

local notation "x[" k "," i "]" =>
  incremental_projected_subgradient_inner_iterate
    C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex t g k x[k] i

include h_problem h_incremental

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] h_problem h_incremental in
/-- Helper for Lemma 8.39: a finite sum of extended-real terms is never `⊥` when no summand is
`⊥`. -/
lemma erealFinsetSum_ne_bot {κ : Type*} (s : Finset κ) (φ : κ → EReal)
    (hφ : ∀ i ∈ s, φ i ≠ ⊥) :
    Finset.sum s φ ≠ ⊥ := by
  classical
  revert hφ
  refine Finset.induction_on s ?_ ?_
  · intro hφ
    simp
  · intro a s ha hs hφ
    rw [Finset.sum_insert ha, EReal.add_ne_bot_iff]
    refine ⟨hφ a (by simp), hs ?_⟩
    intro i hi
    exact hφ i (by simp [hi])

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] h_problem h_incremental in
/-- Helper for Lemma 8.39: a finite sum of extended-real terms stays `< ⊤` when every summand is
`< ⊤`. -/
lemma erealFinsetSum_lt_top {κ : Type*} (s : Finset κ) (φ : κ → EReal)
    (hφ : ∀ i ∈ s, φ i < ⊤) :
    Finset.sum s φ < ⊤ := by
  classical
  revert hφ
  refine Finset.induction_on s ?_ ?_
  · intro hφ
    simp
  · intro a s ha hs hφ
    have ha_top : φ a < ⊤ := hφ a (by simp)
    have hs_top : Finset.sum s φ < ⊤ := hs (fun i hi ↦ hφ i (by simp [hi]))
    rw [Finset.sum_insert ha]
    exact EReal.add_lt_top (lt_top_iff_ne_top.mp ha_top) (lt_top_iff_ne_top.mp hs_top)

omit [CompleteSpace E] h_problem in
/-- Helper for Lemma 8.39: whenever the aggregate finite-sum objective is finite at `x`, each
component value `fi i x` is also finite. -/
lemma componentValue_neTop_of_sumDomain
    {x : E} (hx : x ∈ effective_domain (finite_sum_objective fi)) (i : Fin m) :
    fi i x ≠ ⊤ := by
  have hrest_ne_bot :
      Finset.sum (Finset.univ.erase i) (fun j ↦ fi j x) ≠ ⊥ := by
    -- Properness rules out `⊥` on every remaining component summand.
    exact erealFinsetSum_ne_bot
      (s := Finset.univ.erase i) (φ := fun j ↦ fi j x)
      (fun j _ ↦ (h_incremental.proper j).ne_bot x)
  intro hfi_top
  have hsum :
      Finset.sum Finset.univ (fun j ↦ fi j x) =
        fi i x + Finset.sum (Finset.univ.erase i) (fun j ↦ fi j x) := by
    -- Isolate the `i`-th component from the aggregate finite sum.
    symm
    exact Finset.add_sum_erase Finset.univ (fun j ↦ fi j x) (Finset.mem_univ i)
  have hsum_top : (finite_sum_objective fi) x = ⊤ := by
    -- A `⊤` component forces the whole aggregate objective to be `⊤`.
    rw [finite_sum_objective_apply, hsum, hfi_top, EReal.top_add_of_ne_bot hrest_ne_bot]
  exact (lt_top_iff_ne_top.mp hx) hsum_top

/-- Helper for Lemma 8.39: every feasible point has finite value for each component objective
`fi i`. -/
lemma componentValue_neTop_of_feasible
    {x : E} (hx : x ∈ C) (i : Fin m) :
    fi i x ≠ ⊤ := by
  have hx_sum_dom : x ∈ effective_domain (finite_sum_objective fi) := by
    -- Feasibility places `x` in the interior of the aggregate effective domain.
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hx)
  exact componentValue_neTop_of_sumDomain
    (h_incremental := h_incremental) hx_sum_dom i

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] h_problem h_incremental in
/-- Helper for Lemma 8.39: every finite real sum can be viewed as the corresponding finite sum in
`EReal`. -/
private lemma ereal_coe_finset_sum {κ : Type*} (s : Finset κ) (φ : κ → ℝ) :
    (((Finset.sum s φ : ℝ)) : EReal) = Finset.sum s (fun i ↦ ((φ i : ℝ) : EReal)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · -- The empty sum is preserved by the coercion `ℝ → EReal`.
    simp
  · intro a s ha hs
    -- The coercion commutes with one more real summand.
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add]
    simpa using congrArg (fun t : EReal ↦ (((φ a : ℝ) : EReal) + t)) hs

/-- Helper for Lemma 8.39: on `C`, the aggregate extended-real value is the coercion of the real
sum of the component values. -/
lemma finiteSumObjective_eq_coe_sum_componentToReal
    {x : E} (hx : x ∈ C) :
    (finite_sum_objective fi) x = ((((∑ i : Fin m, (fi i x).toReal) : ℝ)) : EReal) := by
  calc
    (finite_sum_objective fi) x = ∑ i : Fin m, fi i x := by
      -- Expand the aggregate objective into its component sum.
      simp [finite_sum_objective_apply]
    _ = ∑ i : Fin m, (((fi i x).toReal : ℝ) : EReal) := by
      -- Each feasible component value is finite, so it is its own `toReal` coercion.
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [EReal.coe_toReal
        (componentValue_neTop_of_feasible
          (h_problem := h_problem) (h_incremental := h_incremental) hx i)
        ((h_incremental.proper i).ne_bot x)]
    _ = ((((∑ i : Fin m, (fi i x).toReal) : ℝ)) : EReal) := by
      -- Repackage the componentwise `EReal` sum as one coerced real sum.
      symm
      exact ereal_coe_finset_sum
        (s := Finset.univ) (φ := fun i ↦ (fi i x).toReal)

/-- Helper for Lemma 8.39: every feasible point lies in the interior of the effective domain of
each component objective `fi i`. -/
lemma componentInteriorEffectiveDomain_of_feasible
    {x : E} (hx : x ∈ C) (i : Fin m) :
    x ∈ interior (effective_domain (fi i)) := by
  have hx_int :
      x ∈ interior (effective_domain (finite_sum_objective fi)) :=
    h_problem.feasible_subset_interior_effective_domain hx
  refine interior_mono ?_ hx_int
  intro y hy
  exact lt_top_iff_ne_top.mpr
    (componentValue_neTop_of_sumDomain
      (h_incremental := h_incremental) hy i)

/-- Helper for Lemma 8.39: every feasible point has finite value for each component objective
`fi i`. -/
lemma componentEffectiveDomain_of_feasible
    {x : E} (hx : x ∈ C) (i : Fin m) :
    x ∈ effective_domain (fi i) := by
  -- The componentwise finiteness bridge is exactly the non-`⊤` fact proved above.
  exact lt_top_iff_ne_top.mpr
    (componentValue_neTop_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) hx i)

/-- Helper for Lemma 8.39: on the feasible set `C`, the real value of the finite-sum objective is
the sum of the real values of its components. -/
lemma finiteSumObjective_toReal_eq_sum_componentToReal
    {x : E} (hx : x ∈ C) :
    ((finite_sum_objective fi) x).toReal = ∑ i : Fin m, (fi i x).toReal := by
  -- Apply `EReal.toReal` to the stronger aggregate normalization lemma.
  simpa using congrArg EReal.toReal
    (finiteSumObjective_eq_coe_sum_componentToReal
      (h_problem := h_problem) (h_incremental := h_incremental) hx)

/-- Helper for Lemma 8.39: one projected inner update yields the quadratic descent estimate for
the current component objective. -/
lemma incrementalInnerStage_sqdistStep
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (h_stepsize_pos : ∀ n, 0 < t n)
    (k : ℕ) {i : ℕ} (hi : i < m) {xStar : E} (hxStarC : xStar ∈ C) :
    ‖x[k, i + 1] - xStar‖ ^ (2 : ℕ) ≤
      ‖x[k, i] - xStar‖ ^ (2 : ℕ) -
        2 * t k * ((fi ⟨i, hi⟩ x[k, i]).toReal - (fi ⟨i, hi⟩ xStar).toReal) +
          (t k) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ) := by
  let ii : Fin m := ⟨i, hi⟩
  let xki : C := x[k, i]
  let stageDir : E := g k xki ii
  have ht_nonneg : 0 ≤ t k := (h_stepsize_pos k).le
  have hxkip1 :
      x[k, i + 1] =
        metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
          h_problem.feasible_convex ((xki : E) - t k • stageDir) := by
    -- Alias the current stage so the successor rewrite stays short and stable.
    simpa [ii, xki, stageDir] using
      (incremental_projected_subgradient_method_inner_succ
        C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex
        t g x0 k (i := i) hi)
  have hxStar_proj :
      (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
        h_problem.feasible_convex xStar : E) = xStar := by
    -- The comparison point is feasible, so projecting it does nothing.
    simpa [projectionPoint] using
      projectionPoint_eq_self_of_mem C h_problem.feasible_nonempty
        h_problem.feasible_closed h_problem.feasible_convex hxStarC
  have hdist :
      ‖x[k, i + 1] - xStar‖ ≤ ‖((xki : E) - t k • stageDir) - xStar‖ := by
    -- Nonexpansiveness reduces the projected step to the explicit affine update.
    simpa [hxkip1, hxStar_proj, dist_eq_norm] using
      LipschitzWith.dist_le_mul
        (metricProjection_nonexpansive C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex)
        ((xki : E) - t k • stageDir) xStar
  have hsq :
      ‖x[k, i + 1] - xStar‖ ^ (2 : ℕ) ≤ ‖((xki : E) - t k • stageDir) - xStar‖ ^ (2 : ℕ) := by
    -- Squaring preserves the norm inequality because both sides are nonnegative.
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    exact hdist
  have hxki_dom : (xki : E) ∈ effective_domain (fi ii) := by
    -- Every inner iterate stays feasible, hence every component value is finite there.
    exact componentEffectiveDomain_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) xki.property ii
  have hxStar_dom : xStar ∈ effective_domain (fi ii) := by
    -- The same feasible-domain finiteness bridge applies to the comparison point.
    exact componentEffectiveDomain_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) hxStarC ii
  have hsub :
      (toDualMap ℝ E stageDir : Module.Dual ℝ E) ∈ subdifferential (fi ii) (xki : E) := by
    -- Rewrite the selected strong-dual stage direction to the owner subdifferential API.
    simpa [ii, xki, stageDir, mem_strongDualSubdifferential] using h_subgrad k ii
  have hgap_le_inner :
      (fi ii xki).toReal - (fi ii xStar).toReal ≤ inner ℝ ((xki : E) - xStar) stageDir := by
    have hsub_real :
        (toDualMap ℝ E stageDir : Module.Dual ℝ E) (xStar - (xki : E)) ≤
          (fi ii xStar).toReal - (fi ii xki).toReal := by
      -- The componentwise subgradient inequality controls the optimality gap at the stage point.
      exact subgradient_eval_le_toReal_sub (fi ii) (xki : E) xStar
        (fun z hz ↦ (h_incremental.proper ii).ne_bot z) hxki_dom hxStar_dom hsub
    have hinner_neg :
        (toDualMap ℝ E stageDir : Module.Dual ℝ E) (xStar - (xki : E)) =
          -inner ℝ ((xki : E) - xStar) stageDir := by
      change inner ℝ stageDir (xStar - (xki : E)) = -inner ℝ ((xki : E) - xStar) stageDir
      have hrewrite : xStar - (xki : E) = -(((xki : E) - xStar)) := by
        abel
      rw [hrewrite, inner_neg_right, real_inner_comm]
    -- Reorient the displacement so the inner product matches the square-expansion term.
    rw [hinner_neg] at hsub_real
    linarith
  have hstage_norm :
      ‖stageDir‖ ≤ h_incremental.L := by
    have hstrong :
        toDualMap ℝ E stageDir ∈ strongDualSubdifferential (fi ii) (xki : E) := by
      simpa [ii, xki, stageDir] using h_subgrad k ii
    -- Assumption 8.38 bounds every selected component subgradient on the feasible set.
    simpa [stageDir] using
      h_incremental.norm_le (x := (xki : E)) (g := toDualMap ℝ E stageDir) xki.property hstrong
  have hstage_sq :
      ‖stageDir‖ ^ (2 : ℕ) ≤ h_incremental.L ^ (2 : ℕ) := by
    -- Squaring preserves the common norm bound.
    nlinarith [hstage_norm, norm_nonneg stageDir, sq_nonneg h_incremental.L]
  have hexpand :
      ‖((xki : E) - t k • stageDir) - xStar‖ ^ (2 : ℕ) =
        ‖(xki : E) - xStar‖ ^ (2 : ℕ) -
          2 * t k * inner ℝ ((xki : E) - xStar) stageDir +
            (t k) ^ (2 : ℕ) * ‖stageDir‖ ^ (2 : ℕ) := by
    have hrewrite :
        ((xki : E) - t k • stageDir) - xStar = ((xki : E) - xStar) - t k • stageDir := by
      abel
    -- Expand the squared norm of the explicit affine step.
    rw [hrewrite, norm_sub_sq_real]
    rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
    ring
  have hstep_gap :
      ‖((xki : E) - t k • stageDir) - xStar‖ ^ (2 : ℕ) ≤
        ‖(xki : E) - xStar‖ ^ (2 : ℕ) -
          2 * t k * ((fi ii xki).toReal - (fi ii xStar).toReal) +
            (t k) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ) := by
    -- Substitute the subgradient gap bound and the common norm bound into the square expansion.
    rw [hexpand]
    nlinarith
  exact hsq.trans hstep_gap

/-- Helper for Lemma 8.39: the `i`-th inner stage stays within `i * t_k * L` of the outer iterate
`x^k`. -/
lemma incrementalInnerStage_distBase_le
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (h_stepsize_pos : ∀ n, 0 < t n)
    (k : ℕ) :
    ∀ {i : ℕ}, i ≤ m → ‖((x[k, i] : E) - (x[k] : E))‖ ≤ (i : ℝ) * t k * h_incremental.L := by
  intro i hi_le
  induction i with
  | zero =>
      -- Stage `0` is exactly the outer iterate, so the drift vanishes.
      rw [incremental_projected_subgradient_method_inner_zero]
      simp
  | succ i ih =>
      have hi_lt : i < m := Nat.lt_of_succ_le hi_le
      have ht_nonneg : 0 ≤ t k := (h_stepsize_pos k).le
      let ii : Fin m := ⟨i, hi_lt⟩
      let xki : C := x[k, i]
      let stageDir : E := g k xki ii
      have hxki1 :
          x[k, i + 1] =
            metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
              h_problem.feasible_convex ((xki : E) - t k • stageDir) := by
        -- Alias the current stage before rewriting the successor recursion.
        simpa [ii, xki, stageDir] using
          (incremental_projected_subgradient_method_inner_succ
            C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex
            t g x0 k (i := i) hi_lt)
      have hxk_proj :
          (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
            h_problem.feasible_convex (x[k] : E) : E) = (x[k] : E) := by
        -- The outer iterate is feasible, so it is fixed by the projection.
        simpa [projectionPoint] using
          projectionPoint_eq_self_of_mem C h_problem.feasible_nonempty
            h_problem.feasible_closed h_problem.feasible_convex (x[k]).property
      have hdist :
          ‖((x[k, i + 1] : E) - (x[k] : E))‖ ≤
            ‖(((xki : E) - t k • stageDir) - (x[k] : E))‖ := by
        -- Compare the next inner stage to the projection of the base outer iterate.
        simpa [hxki1, hxk_proj, dist_eq_norm] using
          LipschitzWith.dist_le_mul
            (metricProjection_nonexpansive C h_problem.feasible_nonempty
              h_problem.feasible_closed h_problem.feasible_convex)
            ((xki : E) - t k • stageDir) (x[k] : E)
      have htriangle :
          ‖(((xki : E) - t k • stageDir) - (x[k] : E))‖ ≤
            ‖((xki : E) - (x[k] : E))‖ + ‖t k • stageDir‖ := by
        have hrewrite :
            (((xki : E) - t k • stageDir) - (x[k] : E)) =
              ((xki : E) - (x[k] : E)) - t k • stageDir := by
          abel
        -- Separate the inherited drift from the new projected subgradient step.
        rw [hrewrite]
        exact norm_sub_le _ _
      have hstage_norm :
          ‖stageDir‖ ≤ h_incremental.L := by
        have hstrong :
            toDualMap ℝ E stageDir ∈ strongDualSubdifferential (fi ii) (xki : E) := by
          simpa [ii, xki, stageDir] using h_subgrad k ii
        -- Assumption 8.38 bounds the current selected component direction.
        simpa [stageDir] using
          h_incremental.norm_le (x := (xki : E)) (g := toDualMap ℝ E stageDir) xki.property
            hstrong
      have hsmul_norm :
          ‖t k • stageDir‖ ≤ t k * h_incremental.L := by
        -- Positivity of the stepsize turns the scaled norm into a simple product bound.
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
        nlinarith
      have hprev :
          ‖((x[k, i] : E) - (x[k] : E))‖ ≤ (i : ℝ) * t k * h_incremental.L :=
        ih (Nat.le_of_lt hi_lt)
      calc
        ‖((x[k, i + 1] : E) - (x[k] : E))‖ ≤
            ‖(((xki : E) - t k • stageDir) - (x[k] : E))‖ := hdist
        _ ≤ ‖((xki : E) - (x[k] : E))‖ + ‖t k • stageDir‖ := htriangle
        _ ≤ ‖((xki : E) - (x[k] : E))‖ + t k * h_incremental.L := by
          simpa [add_comm] using add_le_add_left hsmul_norm ‖((xki : E) - (x[k] : E))‖
        _ ≤ (i : ℝ) * t k * h_incremental.L + t k * h_incremental.L := by
          simpa [add_comm] using add_le_add_right hprev (t k * h_incremental.L)
        _ = ((i + 1 : ℕ) : ℝ) * t k * h_incremental.L := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

/-- Helper for Lemma 8.39: any strong-dual component subgradient yields the lower directional
derivative bound `-L * ‖d‖ ≤ f'(x; d)` at feasible points. -/
lemma componentDirectionalDerivative_ge_negMulNorm_of_memStrongDualSubgradient
    (i : Fin m) {x d : E} (hx : x ∈ C) {g : StrongDual ℝ E}
    (hg : g ∈ strongDualSubdifferential (fi i) x) :
    (((-(h_incremental.L * ‖d‖) : ℝ)) : EReal) ≤ directional_derivative (fi i) x d := by
  letI : IsProperExtendedRealFunction (fi i) := h_incremental.proper i
  have hx_int :
      x ∈ interior (effective_domain (fi i)) := by
    -- Feasible points lie in the interior effective domain of each component objective.
    exact componentInteriorEffectiveDomain_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) hx i
  have howner : ((g : StrongDual ℝ E) : Module.Dual ℝ E) ∈ subdifferential (fi i) x := by
    -- Read strong-dual subgradient membership through the owner predicate.
    simpa [mem_strongDualSubdifferential] using hg
  have hpair :
      (((g : StrongDual ℝ E) : Module.Dual ℝ E) d : EReal) ≤
        directional_derivative (fi i) x d := by
    -- Every owner subgradient pairing is bounded above by the directional derivative.
    exact subgradientPairing_leDirectionalDerivative
      (h_incremental.convex i) hx_int howner
  have hnorm : ‖g‖ ≤ h_incremental.L :=
    h_incremental.norm_le hx hg
  have habs : |g d| ≤ h_incremental.L * ‖d‖ := by
    calc
      |g d| = ‖g d‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖g‖ * ‖d‖ := by simpa using (ContinuousLinearMap.le_opNorm g d)
      _ ≤ h_incremental.L * ‖d‖ := by gcongr
  have hlower : -(h_incremental.L * ‖d‖) ≤ g d := by
    -- The operator-norm estimate bounds the chosen pairing from below.
    linarith [neg_abs_le (g d), habs]
  exact le_trans (by exact_mod_cast hlower) hpair

/-- Helper for Lemma 8.39: the selected stage subgradient gives the same lower directional
derivative bound at the current inner iterate. -/
lemma selectedStageDirectionalDerivative_ge_negMulNorm
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (k : ℕ) {i : ℕ} (hi : i < m) :
    (((-(h_incremental.L * ‖((x[k] : E) - (x[k, i] : E))‖) : ℝ)) : EReal) ≤
      directional_derivative (fi ⟨i, hi⟩) (x[k, i] : E) ((x[k] : E) - (x[k, i] : E)) := by
  let ii : Fin m := ⟨i, hi⟩
  let xki : C := x[k, i]
  let stageDir : E := g k xki ii
  have hstrong :
      toDualMap ℝ E stageDir ∈ strongDualSubdifferential (fi ii) (xki : E) := by
    -- Specialize the selected subgradient hypothesis to the current stage index.
    simpa [ii, xki, stageDir] using h_subgrad k ii
  exact componentDirectionalDerivative_ge_negMulNorm_of_memStrongDualSubgradient
    (h_problem := h_problem) (h_incremental := h_incremental) ii xki.property hstrong

variable [FiniteDimensional ℝ E]

/-- Helper for Lemma 8.39: the component value at the `i`-th inner stage is bounded below by the
same component value at the outer iterate `x^k`, up to the stage drift term. -/
lemma componentGap_compare_toOuterIterate
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (k : ℕ) {i : ℕ} (hi : i < m) {xStar : E} :
    (fi ⟨i, hi⟩ x[k, i]).toReal - (fi ⟨i, hi⟩ xStar).toReal ≥
      (fi ⟨i, hi⟩ x[k]).toReal - (fi ⟨i, hi⟩ xStar).toReal -
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
  let ii : Fin m := ⟨i, hi⟩
  have hLip :
      LipschitzOnWith (Real.toNNReal h_incremental.L) (fun z ↦ (fi ii z).toReal) C := by
    -- The bounded-subgradient hypothesis makes each component objective Lipschitz on `C`.
    refine lipschitzOnWith_toReal_of_subdifferential_norm_le_on
        (f := fi ii) (X := C) (L := Real.toNNReal h_incremental.L)
        (fun z _ ↦ (h_incremental.proper ii).ne_bot z) (h_incremental.convex ii) ?_ ?_
    · intro z hz
      exact componentInteriorEffectiveDomain_of_feasible
        (h_problem := h_problem) (h_incremental := h_incremental) hz ii
    · intro z gz hz hgz
      simpa [Real.toNNReal_of_nonneg h_incremental.L_pos.le] using
        (h_incremental.norm_le (i := ii) hz hgz)
  have hvalueDiff :
      (fi ii x[k]).toReal - (fi ii x[k, i]).toReal ≤
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
    have habs :
        |(fi ii x[k]).toReal - (fi ii x[k, i]).toReal| ≤
          (Real.toNNReal h_incremental.L : ℝ) * dist (x[k] : E) (x[k, i] : E) := by
      exact abs_toReal_sub_le_mul_dist_of_lipschitzOnWith
        (f := fi ii) hLip (x[k, i]).property (x[k]).property
    have hle :
        (fi ii x[k]).toReal - (fi ii x[k, i]).toReal ≤
          |(fi ii x[k]).toReal - (fi ii x[k, i]).toReal| :=
      le_abs_self _
    exact le_trans hle (by
      simpa [Real.toNNReal_of_nonneg h_incremental.L_pos.le, dist_eq_norm, norm_sub_rev] using
        habs)
  -- Keep the comparison-point term fixed and isolate the controllable stage drift.
  linarith

-- Proof sketch: apply the one-step projected subgradient inequality to each inner update
-- `x[k,i+1] = P_C (x[k,i] - t_k g^{k,i})`, sum over the `m` component steps, rewrite the summed
-- component objectives as the finite-sum objective, and bound the accumulated error terms with the
-- common subgradient norm constant `h_incremental.L` from Assumption 8.38.
/-- Lemma 8.39: under Assumptions 8.7 and 8.38, every outer step of the incremental projected
subgradient method with positive stepsizes satisfies the fundamental inequality
`‖x^{k+1} - xStar‖^2 ≤ ‖x^k - xStar‖^2 - 2 t_k (f(x^k) - fOpt) + t_k^2 m^2 L^2`
for each optimal point `xStar ∈ XStar`, where `f = ∑ i, f_i` and `L = h_incremental.L`. -/
theorem incremental_projected_subgradient_method_fundamental_inequality
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (h_stepsize_pos : ∀ n, 0 < t n)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖x[k + 1] - xStar‖ ^ (2 : ℕ) ≤
      ‖x[k] - xStar‖ ^ (2 : ℕ) -
        2 * t k * ((finite_sum_objective fi x[k]).toReal - fOpt) +
          (t k) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ) := by
  have hxStar_data : xStar ∈ C ∧ IsMinOn (finite_sum_objective fi) C xStar := by
    -- Optimal-set membership provides the feasible comparison point used throughout the proof.
    simpa [h_problem.optimal_set_eq] using hxStar
  have hcum :
      ∀ {j : ℕ}, j ≤ m →
        ‖x[k, j] - xStar‖ ^ (2 : ℕ) ≤
          ‖x[k] - xStar‖ ^ (2 : ℕ) -
            2 * t k *
              Finset.sum (Finset.range j) (fun r ↦
                if hr : r < m then
                  (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
                else 0) +
              (t k) ^ (2 : ℕ) * (j : ℝ) * h_incremental.L ^ (2 : ℕ) := by
    intro j hj
    induction j with
    | zero =>
        -- At stage `0` no inner update has been performed, so the cumulative bound is exact.
        rw [incremental_projected_subgradient_method_inner_zero]
        simp
    | succ j ih =>
        have hj_lt : j < m := Nat.lt_of_succ_le hj
        have hstep :=
          incrementalInnerStage_sqdistStep
            (h_problem := h_problem) (h_incremental := h_incremental)
            (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_pos
            (k := k) (i := j) hj_lt (xStar := xStar) hxStar_data.1
        have hprev := ih (Nat.le_of_lt hj_lt)
        have hsum :
            Finset.sum (Finset.range (j + 1)) (fun r ↦
                if hr : r < m then
                  (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
                else 0) =
              Finset.sum (Finset.range j) (fun r ↦
                  if hr : r < m then
                    (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
                  else 0) +
                ((fi ⟨j, hj_lt⟩ x[k, j]).toReal - (fi ⟨j, hj_lt⟩ xStar).toReal) := by
          -- The next cumulative sum appends exactly the current component gap.
          rw [Finset.sum_range_succ]
          simp [hj_lt]
        calc
          ‖x[k, j + 1] - xStar‖ ^ (2 : ℕ) ≤
              ‖x[k, j] - xStar‖ ^ (2 : ℕ) -
                2 * t k * ((fi ⟨j, hj_lt⟩ x[k, j]).toReal - (fi ⟨j, hj_lt⟩ xStar).toReal) +
                  (t k) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ) := hstep
          _ ≤ ‖x[k] - xStar‖ ^ (2 : ℕ) -
                2 * t k *
                  (Finset.sum (Finset.range j) (fun r ↦
                      if hr : r < m then
                        (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
                      else 0) +
                    ((fi ⟨j, hj_lt⟩ x[k, j]).toReal - (fi ⟨j, hj_lt⟩ xStar).toReal)) +
                  ((t k) ^ (2 : ℕ) * (j : ℝ) * h_incremental.L ^ (2 : ℕ) +
                    (t k) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) := by
            nlinarith [hprev]
          _ = ‖x[k] - xStar‖ ^ (2 : ℕ) -
                2 * t k *
                  Finset.sum (Finset.range (j + 1)) (fun r ↦
                    if hr : r < m then
                      (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
                    else 0) +
                  (t k) ^ (2 : ℕ) * ((j + 1 : ℕ) : ℝ) * h_incremental.L ^ (2 : ℕ) := by
            rw [hsum, Nat.cast_add, Nat.cast_one]
            ring
  have hcum_m :
      ‖x[k + 1] - xStar‖ ^ (2 : ℕ) ≤
          ‖x[k] - xStar‖ ^ (2 : ℕ) -
          2 * t k *
            Finset.sum (Finset.range m) (fun r ↦
              if hr : r < m then
                (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
              else 0) +
            (t k) ^ (2 : ℕ) * (m : ℝ) * h_incremental.L ^ (2 : ℕ) := by
    -- The outer iterate `x[k + 1]` is the final inner stage `x[k,m]`.
    simpa [incremental_projected_subgradient_method_succ
      C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex
      t g x0 k] using
      (hcum (j := m) le_rfl)
  have hstageSumEq :
      Finset.sum (Finset.range m) (fun r ↦
          if hr : r < m then
            (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
          else 0) =
        Finset.sum Finset.univ (fun i : Fin m ↦ ((fi i x[k, i.1]).toReal - (fi i xStar).toReal)) := by
    -- Reindex the range sum by `Fin m` so the component objective identities apply directly.
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp
  have hgapSum :
      Finset.sum Finset.univ (fun i : Fin m ↦
        ((fi i x[k, i.1]).toReal - (fi i xStar).toReal)) ≥
        ((finite_sum_objective fi x[k]).toReal - fOpt) -
          (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) * t k * h_incremental.L ^ (2 : ℕ) := by
    have hpoint :
        ∀ i : Fin m,
          (fi i x[k]).toReal - (fi i xStar).toReal ≤
            ((fi i x[k, i.1]).toReal - (fi i xStar).toReal) +
              (i : ℝ) * t k * h_incremental.L ^ (2 : ℕ) := by
      intro i
      have hcomp :=
        componentGap_compare_toOuterIterate
          (h_problem := h_problem) (h_incremental := h_incremental)
          (g := g) (t := t) (x0 := x0) h_subgrad
          (k := k) (i := i.1) i.2 (xStar := xStar)
      have hdist :=
        incrementalInnerStage_distBase_le
          (h_problem := h_problem) (h_incremental := h_incremental)
          (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_pos
          (k := k) (i := i.1) (Nat.le_of_lt i.2)
      have hdrift :
          h_incremental.L * ‖((x[k, i.1] : E) - (x[k] : E))‖ ≤
            (i : ℝ) * t k * h_incremental.L ^ (2 : ℕ) := by
        -- The inner-stage drift is at most `i * t_k * L`, so multiplying by `L` gives `i t_k L^2`.
        nlinarith [hdist, h_stepsize_pos k, h_incremental.L_pos]
      linarith
    have hsumPoint :
        Finset.sum Finset.univ (fun i : Fin m ↦ ((fi i x[k]).toReal - (fi i xStar).toReal)) ≤
          Finset.sum Finset.univ (fun i : Fin m ↦
            (((fi i x[k, i.1]).toReal - (fi i xStar).toReal) +
              (i : ℝ) * t k * h_incremental.L ^ (2 : ℕ))) := by
      -- Sum the componentwise comparison after inserting the controlled drift term.
      exact Finset.sum_le_sum (fun i _ ↦ hpoint i)
    have houterEq :
        Finset.sum Finset.univ (fun i : Fin m ↦ ((fi i x[k]).toReal - (fi i xStar).toReal)) =
          (finite_sum_objective fi x[k]).toReal - fOpt := by
      have hxStarSum :
          Finset.sum Finset.univ (fun i : Fin m ↦ (fi i xStar).toReal) = fOpt := by
        calc
          Finset.sum Finset.univ (fun i : Fin m ↦ (fi i xStar).toReal) =
              (finite_sum_objective fi xStar).toReal := by
            symm
            exact finiteSumObjective_toReal_eq_sum_componentToReal
              (h_problem := h_problem) (h_incremental := h_incremental)
              (x := xStar) hxStar_data.1
          _ = fOpt := optimal_point_toReal_eq_fOpt h_problem hxStar
      -- Collapse the component sum at `x[k]` and the optimal-point sum at `xStar`.
      rw [Finset.sum_sub_distrib,
        finiteSumObjective_toReal_eq_sum_componentToReal
          (h_problem := h_problem) (h_incremental := h_incremental)
          (x := (x[k] : E)) (x[k]).property,
        hxStarSum]
    have hdriftSum :
        Finset.sum Finset.univ (fun i : Fin m ↦ (i : ℝ) * t k * h_incremental.L ^ (2 : ℕ)) =
          (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) * t k * h_incremental.L ^ (2 : ℕ) := by
      calc
        Finset.sum Finset.univ (fun i : Fin m ↦ (i : ℝ) * t k * h_incremental.L ^ (2 : ℕ)) =
            Finset.sum Finset.univ (fun i : Fin m ↦ (i : ℝ) * (t k * h_incremental.L ^ (2 : ℕ))) := by
          simp [mul_assoc]
        _ = (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) * (t k * h_incremental.L ^ (2 : ℕ)) := by
          simpa using
            (Finset.sum_mul (s := Finset.univ)
              (f := fun i : Fin m ↦ (i : ℝ)) (a := t k * h_incremental.L ^ (2 : ℕ))).symm
        _ = (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) * t k * h_incremental.L ^ (2 : ℕ) := by
          ring
    rw [houterEq, Finset.sum_add_distrib, hdriftSum] at hsumPoint
    linarith
  have hindexSum :
      (2 : ℝ) * (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) + m = (m : ℝ) ^ (2 : ℕ) := by
    -- The textbook coefficient identity `2 * ∑_{i=0}^{m-1} i + m = m^2` closes the error term.
    have hdoubleNat : 2 * Finset.sum (Finset.range m) (fun i ↦ i) = m * (m - 1) := by
      calc
        2 * Finset.sum (Finset.range m) (fun i ↦ i) = 2 * (m * (m - 1) / 2) := by
          rw [Finset.sum_range_id]
        _ = m * (m - 1) := by
          rw [← Nat.mul_div_assoc 2 (Nat.even_mul_pred_self m).two_dvd]
          simp
    have hsumCast :
        Finset.sum (Finset.range m) (fun i ↦ (i : ℝ)) =
          ((Finset.sum (Finset.range m) fun i ↦ i : ℕ) : ℝ) := by
      norm_num
    have hindexRange :
        (2 : ℝ) * Finset.sum (Finset.range m) (fun i ↦ (i : ℝ)) + m = (m : ℝ) ^ (2 : ℕ) := by
      have hdoubleRange :
          (2 : ℝ) * Finset.sum (Finset.range m) (fun i ↦ (i : ℝ)) =
            ((m * (m - 1) : ℕ) : ℝ) := by
        rw [hsumCast]
        exact_mod_cast hdoubleNat
      calc
        (2 : ℝ) * Finset.sum (Finset.range m) (fun i ↦ (i : ℝ)) + m =
            ((m * (m - 1) : ℕ) : ℝ) + m := by
          rw [hdoubleRange]
        _ = (m : ℝ) ^ (2 : ℕ) := by
          cases m with
          | zero =>
              norm_num
          | succ n =>
              simp [Nat.cast_add, Nat.cast_one]
              ring
    simpa [Fin.sum_univ_eq_sum_range] using hindexRange
  calc
    ‖x[k + 1] - xStar‖ ^ (2 : ℕ) ≤
        ‖x[k] - xStar‖ ^ (2 : ℕ) -
          2 * t k * ((finite_sum_objective fi x[k]).toReal - fOpt) +
            (t k) ^ (2 : ℕ) *
              (((2 : ℝ) * (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) + m) *
                h_incremental.L ^ (2 : ℕ)) := by
      -- Combine the cumulative descent estimate with the objective-gap lower bound on the stage sum.
      rw [hstageSumEq] at hcum_m
      nlinarith [hcum_m, hgapSum, h_stepsize_pos k, h_incremental.L_pos]
    _ = ‖x[k] - xStar‖ ^ (2 : ℕ) -
          2 * t k * ((finite_sum_objective fi x[k]).toReal - fOpt) +
            (t k) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ) := by
      rw [hindexSum]
      ring

end

end
