/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_47
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_28
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_40

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped StrongConvex

section StronglyConvexProblemClass

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- Theorem 3.47 lies in the strongly convex first-order black-box complexity domain.

Sampled owner-style declarations:
* `S0On` / `mem_S0On_iff` in `Definition_3_47`
* mathlib `StrongConvexOn`
* `IsInLipschitzConvexProblemClass` in `Theorem_3_2_1`
* `bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn`
  in `Theorem_3_2_6`
* `FirstOrderOracle`, `HasCoordinateSupportGrowth`, and `SatisfiesLinearSpanCondition` in
  `Theorem_3_2_1`

Best owner abstraction:
* source-facing: the local-ball class `𝒫_s(x₀, μ, M)` on a real normed space
* core/canonical: membership in `𝒮^0_(μ : ℝ)(B₂(x*, ‖x₀ - x*‖))`, together with
  `IsMinOn f Set.univ xStar` and the ballwise `LipschitzOnWith M f`
* bridge/view: projected-subgradient and oracle/span lower-bound theorems built from that class;
  only the hard-instance oracle lower bound specializes to `ℝⁿ`

Primitive data:
* the objective `f : V → ℝ`
* the chosen minimizer `xStar : V`

Derived API:
* positivity of `μ` and strong convexity on the controlling ball via the Chapter 3 owner
  `𝒮^0_μ(Q)`
* positivity of `M`, global minimality at `xStar`, and the ballwise Lipschitz bound
* downstream projected-subgradient and hard-instance lower-bound theorems

Source/core/bridge triage:
* source-facing: `𝒫_s(x₀, μ, M)`
* core/canonical: `f ∈ 𝒮^0_((μ : ℝ))(Metric.closedBall xStar ‖x0 - xStar‖)`
* bridge/view: the projected-subgradient theorem on real inner-product spaces and the separate
  Euclidean hard-instance lower bound

The previous version stored the strong-convexity part as a second local conjunction
`0 < μ ∧ StrongConvexOn ...`. This file now reuses the chapter owner `𝒮^0_μ(Q)` directly and
keeps the local-ball class itself as the only source-facing wrapper, at the same normed-space
abstraction level already used by `𝒫(x₀, R, M)`. -/

/-- A function together with a chosen point `x*` lies in the strongly convex class
`𝒫_s(x₀, μ, M)` when `μ > 0`, `M > 0`, the objective belongs to `𝒮^0_μ` on the closed ball
`B₂(x*, ‖x₀ - x*‖)`, `x*` is a global minimizer, and the function is `M`-Lipschitz on that same
ball. -/
def IsInStronglyConvexProblemClass
    (x0 : V) (μ M : NNReal) (f : V → ℝ) (xStar : V) : Prop :=
  let Q : Set V := Metric.closedBall xStar ‖x0 - xStar‖
  f ∈ 𝒮^0_((μ : ℝ))(Q) ∧
    0 < M ∧
    IsMinOn f Set.univ xStar ∧
    LipschitzOnWith M f Q

scoped[StronglyConvexProblemClass] notation "𝒫_s(" x0 ", " μ ", " M ")" =>
  IsInStronglyConvexProblemClass x0 μ M

open scoped StronglyConvexProblemClass

namespace IsInStronglyConvexProblemClass

variable {x0 : V} {μ M : NNReal} {f : V → ℝ} {xStar : V}

local notation "Q" => (Metric.closedBall xStar ‖x0 - xStar‖ : Set V)

/-- Membership in `𝒫_s(x₀, μ, M)` records `𝒮^0_μ` membership on the controlling closed ball. -/
theorem mem_S0On_closedBall
    (hf : 𝒫_s(x0, μ, M) f xStar) :
    f ∈ 𝒮^0_((μ : ℝ))(Q) :=
  hf.1

/-- Membership in `𝒫_s(x₀, μ, M)` records positivity of the strong-convexity parameter. -/
theorem mu_pos
    (hf : 𝒫_s(x0, μ, M) f xStar) :
    0 < μ := by
  exact hf.1.1

/-- Membership in `𝒫_s(x₀, μ, M)` records positivity of the Lipschitz constant. -/
theorem lipschitzConst_pos
    (hf : 𝒫_s(x0, μ, M) f xStar) :
    0 < M :=
  hf.2.1

/-- Membership in `𝒫_s(x₀, μ, M)` yields the canonical strong-convexity owner on the controlling
closed ball. -/
theorem strongConvexOn_closedBall
    (hf : 𝒫_s(x0, μ, M) f xStar) :
    StrongConvexOn Q (μ : ℝ) f :=
  hf.1.2

/-- Membership in `𝒫_s(x₀, μ, M)` records that the chosen point `x*` globally minimizes the
objective. -/
-- Proof sketch: unfold `IsInStronglyConvexProblemClass` and project to the `IsMinOn` component.
theorem isMinOn
    (hf : 𝒫_s(x0, μ, M) f xStar) :
    IsMinOn f Set.univ xStar :=
  hf.2.2.1

/-- Membership in `𝒫_s(x₀, μ, M)` records `M`-Lipschitz continuity on the controlling closed
ball. -/
theorem lipschitzOn_closedBall
    (hf : 𝒫_s(x0, μ, M) f xStar) :
    LipschitzOnWith M f Q :=
  hf.2.2.2

end IsInStronglyConvexProblemClass

end StronglyConvexProblemClass

section EuclideanLowerBound

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open scoped StronglyConvexProblemClass CoordinateSubspace WithTopConvexAnalysis

/-- Helper for Theorem 3.47: the maximum of the first `m` coordinates is convex on all of
`ℝ^n`. -/
theorem first_k_coordinate_max_convexOn_univ
    {m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    ConvexOn ℝ Set.univ (first_k_coordinate_max n m) := by
  letI : Nonempty (FirstKIndex n m) := firstKIndex_nonempty hm hmn
  let Φ : E → WithTop ℝ :=
    pointwiseSupremumOn (Set.univ : Set (FirstKIndex n m)) (firstKCoordinateFamily n m)
  have hΦ : ClosedConvexFunction Φ := by
    -- The prefix maximum is the finite `Set.univ` supremum of coordinate slices.
    exact closedConvexFunction_pointwiseSupremumOn_univ
      (fun i ↦ firstKCoordinate_slice_closedConvexFunction (n := n) (k := m) i)
  have hconv : ConvexOn ℝ (dom Φ) (withTopRealPart Φ) :=
    ClosedConvexOn.convexOn_withTopRealPart hΦ
  have hdom : dom Φ = Set.univ := by
    -- For a nonempty prefix, the restricted supremum is finite everywhere.
    simpa [Φ] using firstKCoordinateSup_dom_eq_univ (n := n) (k := m) hm hmn
  have hfun : withTopRealPart Φ = first_k_coordinate_max n m := by
    funext x
    have hx : x ∈ dom Φ := by
      simp [hdom]
    -- On the effective domain, `withTopRealPart` recovers the real-valued prefix maximum.
    have hcoe :
        ((withTopRealPart Φ x : ℝ) : WithTop ℝ) =
          ((first_k_coordinate_max n m x : ℝ) : WithTop ℝ) := by
      rw [coe_withTopRealPart hx]
      simpa [Φ] using
        (coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ (n := n) (k := m) (x := x)).symm
    exact_mod_cast hcoe
  convert (show ConvexOn ℝ Set.univ (withTopRealPart Φ) from by simpa [hdom] using hconv) using 1
  exact hfun.symm

/-- Helper for Theorem 3.47: translating the hard instance by `x₀` preserves the required
`μ`-strong convexity on the controlling closed ball. -/
theorem translated_hard_instance_strongConvexOn_closedBall
    (x0 : E) (μ M : NNReal) (_hμ : 0 < μ) {k : ℕ} (hk : k + 1 ≤ n) :
    let γ : ℝ := (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))
    let zStar : E := f_k_minimizer n (k + 1) (μ : ℝ) γ
    let xStar : E := x0 + zStar
    let f : E → ℝ := fun x ↦ f_k n (k + 1) (μ : ℝ) γ (x - x0)
    StrongConvexOn (Metric.closedBall xStar ‖x0 - xStar‖) (μ : ℝ) f := by
  dsimp
  have hγ_nonneg :
      0 ≤ (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)) := by
    positivity
  have hstrong_untranslated :
      StrongConvexOn Set.univ (μ : ℝ)
        (fun x : E ↦
          f_k n (k + 1) (μ : ℝ)
            ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) x) := by
    rw [strongConvexOn_iff_convex]
    have hbase :
        ConvexOn ℝ Set.univ (first_k_coordinate_max n (k + 1)) :=
      first_k_coordinate_max_convexOn_univ (n := n) (m := k + 1) (Nat.succ_pos k) hk
    -- On the untranslated model, subtracting the quadratic term leaves only the convex prefix
    -- maximum.
    simpa [f_k_def, smul_eq_mul] using hbase.smul hγ_nonneg
  refine ⟨convex_closedBall _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have htranslated :
      a • (x - x0) + b • (y - x0) = a • x + b • y - x0 := by
    calc
      a • (x - x0) + b • (y - x0) = a • x + b • y - (a • x0 + b • x0) := by
        rw [smul_sub, smul_sub]
        abel
      _ = a • x + b • y - x0 := by
        rw [← add_smul, hab, one_smul]
  have hsub : (x - x0) - (y - x0) = x - y := by
    abel
  have h :=
    hstrong_untranslated.2 (x := x - x0) (by simp) (y := y - x0) (by simp) ha hb hab
  -- Translation preserves the strong-convexity inequality because affine shifts cancel in the
  -- convex combination and in the difference `x - y`.
  simpa [f_k_def, htranslated, hsub, smul_eq_mul] using h

/-- Helper for Theorem 3.47: the translated hard instance is globally minimized at the translated
explicit minimizer. -/
theorem translated_hard_instance_isMinOn
    (x0 : E) (μ M : NNReal) (hμ : 0 < μ) {k : ℕ} (hk : k + 1 ≤ n) :
    let γ : ℝ := (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))
    let zStar : E := f_k_minimizer n (k + 1) (μ : ℝ) γ
    let xStar : E := x0 + zStar
    let f : E → ℝ := fun x ↦ f_k n (k + 1) (μ : ℝ) γ (x - x0)
    IsMinOn f Set.univ xStar := by
  dsimp
  have hγ_nonneg :
      0 ≤ (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)) := by
    positivity
  have hmin :
      IsMinOn
        (f_k n (k + 1) (μ : ℝ)
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))))
        Set.univ
        (f_k_minimizer n (k + 1) (μ : ℝ)
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))) := by
    -- The explicit minimizer from Proposition 3.30 closes the untranslated problem.
    simpa using
      isMinOn_f_k_minimizer (n := n) (k := k + 1) (μ := (μ : ℝ))
        (γ := (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))
        (Nat.succ_pos k) hk (show 0 < (μ : ℝ) by exact_mod_cast hμ) hγ_nonneg
  rw [isMinOn_univ_iff] at hmin ⊢
  intro x
  -- Translation does not change the comparison against the global minimizer.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmin (x - x0)

/-- Helper for Theorem 3.47: every subgradient of the translated hard instance on the controlling
closed ball has norm at most `M`. -/
theorem translated_hard_instance_lipschitzOn_closedBall
    (x0 : E) (μ M : NNReal) (hμ : 0 < μ) {k : ℕ} (hk : k + 1 ≤ n) :
    let γ : ℝ := (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))
    let zStar : E := f_k_minimizer n (k + 1) (μ : ℝ) γ
    let xStar : E := x0 + zStar
    let f : E → ℝ := fun x ↦ f_k n (k + 1) (μ : ℝ) γ (x - x0)
    LipschitzOnWith M f (Metric.closedBall xStar ‖x0 - xStar‖) := by
  dsimp
  have hγ_nonneg :
      0 ≤ (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)) := by
    positivity
  have hz_norm :
      ‖f_k_minimizer n (k + 1) (μ : ℝ)
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))‖ =
        ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) /
          ((μ : ℝ) * Real.sqrt (k + 1)) := by
    -- Proposition 3.30 gives the exact radius of the hard-instance minimizer.
    simpa using
      f_k_minimizer_norm_eq (n := n) (k := k + 1) (μ := (μ : ℝ))
        (γ := (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))
        (Nat.succ_pos k) hk (show 0 < (μ : ℝ) by exact_mod_cast hμ) hγ_nonneg
  refine LipschitzOnWith.of_le_add_mul M ?_
  intro x hx y hy
  let activeHull : Set E :=
    convexHull ℝ
      ((fun i : FirstKIndex n (k + 1) ↦ EuclideanSpace.single i.1 (1 : ℝ)) ''
        activePointwiseSupremumOnIndices
          (Set.univ : Set (FirstKIndex n (k + 1)))
          (firstKCoordinateFamily n (k + 1)) (x - x0))
  have hHull_nonempty : activeHull.Nonempty := by
    -- The active prefix basis hull is nonempty because some active coordinate always exists.
    simpa [activeHull] using
      convexHull_activeBasis_nonempty (n := n) (k := k + 1) (Nat.succ_pos k) hk (x - x0)
  rcases hHull_nonempty with ⟨v, hv⟩
  have hg :
      (μ : ℝ) • (x - x0) +
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v ∈
        subdifferential
          (fun z : E ↦
            (f_k n (k + 1) (μ : ℝ)
              ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) z : WithTop ℝ))
          (x - x0) := by
    -- Proposition 3.28 identifies the full subdifferential as the affine image of that hull.
    rw [subdifferential_f_k_eq_affineImage_convexHull_activeBasis (n := n) (k := k + 1)
      ((μ : ℝ)) (((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))
      ) (Nat.succ_pos k) hk (show 0 ≤ (μ : ℝ) by exact_mod_cast hμ.le) hγ_nonneg (x - x0)]
    exact ⟨v, hv, rfl⟩
  have hy_dom :
      y - x0 ∈
        dom
          (fun z : E ↦
            (f_k n (k + 1) (μ : ℝ)
              ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) z : WithTop ℝ)) := by
    change
      (((f_k n (k + 1) (μ : ℝ)
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (y - x0) : ℝ) :
        WithTop ℝ) < ⊤)
    exact WithTop.coe_lt_top _
  have hsupport_top := (mem_subdifferential_iff.mp hg).2 hy_dom
  have hsupport :
      f_k n (k + 1) (μ : ℝ)
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (x - x0) -
        f_k n (k + 1) (μ : ℝ)
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (y - x0) ≤
      inner ℝ
        ((μ : ℝ) • (x - x0) +
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v)
        ((x - x0) - (y - x0)) := by
    have hsupport_real :
        f_k n (k + 1) (μ : ℝ)
            ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (x - x0) +
          inner ℝ
            ((μ : ℝ) • (x - x0) +
              ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v)
            ((y - x0) - (x - x0)) ≤
          f_k n (k + 1) (μ : ℝ)
            ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (y - x0) := by
      have hsupport_withTop :
          (((f_k n (k + 1) (μ : ℝ)
              ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (x - x0) +
            inner ℝ
              ((μ : ℝ) • (x - x0) +
                ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v)
              ((y - x0) - (x - x0)) : ℝ) : WithTop ℝ)) ≤
            (f_k n (k + 1) (μ : ℝ)
              ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (y - x0) :
                WithTop ℝ) := by
        simpa using hsupport_top
      exact_mod_cast hsupport_withTop
    have hswap :
        (y - x0) - (x - x0) = -((x - x0) - (y - x0)) := by
      abel
    rw [hswap, inner_neg_right] at hsupport_real
    linarith
  have hv_ball : v ∈ Metric.closedBall (0 : E) 1 :=
    (convexHull_min
      (by
        intro u hu
        rcases hu with ⟨i, -, rfl⟩
        simp [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.single])
      (convex_closedBall (0 : E) (1 : ℝ))) hv
  have hv_norm : ‖v‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv_ball
  have hx_norm :
      ‖x - x0‖ ≤
        2 *
          ‖f_k_minimizer n (k + 1) (μ : ℝ)
            ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))‖ := by
    -- The control ball around `xStar` sits inside the radius-`2R` ball around `x₀`.
    calc
      ‖x - x0‖ ≤
          ‖x -
              (x0 +
                f_k_minimizer n (k + 1) (μ : ℝ)
                  ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))))‖ +
            ‖(x0 +
                f_k_minimizer n (k + 1) (μ : ℝ)
                  ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))) - x0‖ := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              norm_add_le
                (x -
                  (x0 +
                    f_k_minimizer n (k + 1) (μ : ℝ)
                      ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))))
                )
                ((x0 +
                    f_k_minimizer n (k + 1) (μ : ℝ)
                      ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))) - x0)
      _ ≤
          ‖x0 -
              (x0 +
                f_k_minimizer n (k + 1) (μ : ℝ)
                  ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))))‖ +
            ‖f_k_minimizer n (k + 1) (μ : ℝ)
                ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))‖ := by
            gcongr
            · simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_assoc,
                add_left_comm, add_comm] using hx
            · simp
      _ =
          2 *
            ‖f_k_minimizer n (k + 1) (μ : ℝ)
              ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))‖ := by
            have hsub :
                x0 -
                    (x0 +
                      f_k_minimizer n (k + 1) (μ : ℝ)
                        ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))) =
                  -(f_k_minimizer n (k + 1) (μ : ℝ)
                    ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))) := by
              abel
            rw [hsub, norm_neg]
            ring
  have hgrad_norm :
      ‖(μ : ℝ) • (x - x0) +
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v‖ ≤
        M := by
    have haux :
        ‖(μ : ℝ) • (x - x0) +
            ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v‖ ≤
          (μ : ℝ) * ‖x - x0‖ +
            ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) * ‖v‖ := by
      -- Split the translated subgradient into its quadratic and active-basis pieces.
      calc
        ‖(μ : ℝ) • (x - x0) +
            ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v‖ ≤
          ‖(μ : ℝ) • (x - x0)‖ +
            ‖((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v‖ := norm_add_le _ _
        _ =
            (μ : ℝ) * ‖x - x0‖ +
              ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) * ‖v‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (show 0 ≤ (μ : ℝ) by
                exact_mod_cast hμ.le), Real.norm_of_nonneg hγ_nonneg]
    have hbound_quad :
        (μ : ℝ) * ‖x - x0‖ ≤
          (μ : ℝ) *
            (2 *
              ‖f_k_minimizer n (k + 1) (μ : ℝ)
                ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))‖) := by
      gcongr
    have hbound_active :
        ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) * ‖v‖ ≤
          (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)) := by
      nlinarith [hv_norm, hγ_nonneg]
    calc
      ‖(μ : ℝ) • (x - x0) +
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v‖ ≤
        (μ : ℝ) * ‖x - x0‖ +
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) * ‖v‖ := haux
      _ ≤
          (μ : ℝ) *
              (2 *
                ‖f_k_minimizer n (k + 1) (μ : ℝ)
                  ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))‖) +
            (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)) := by
            linarith
      _ = M := by
          rw [hz_norm]
          field_simp [show (μ : ℝ) ≠ 0 by exact_mod_cast hμ.ne']
  -- Feed the bounded translated subgradient into the standard one-sided Lipschitz criterion.
  calc
    f_k n (k + 1) (μ : ℝ)
        ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (x - x0) ≤
      f_k n (k + 1) (μ : ℝ)
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (y - x0) +
        M * dist x y := by
          have hinner :
              inner ℝ
                  ((μ : ℝ) • (x - x0) +
                    ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v)
                  ((x - x0) - (y - x0)) ≤
                M * dist x y := by
            calc
              inner ℝ
                  ((μ : ℝ) • (x - x0) +
                    ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v)
                  ((x - x0) - (y - x0)) ≤
                ‖(μ : ℝ) • (x - x0) +
                    ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) • v‖ *
                  ‖(x - x0) - (y - x0)‖ := real_inner_le_norm _ _
              _ ≤ M * ‖(x - x0) - (y - x0)‖ := by
                    gcongr
              _ = M * dist x y := by
                    simp [dist_eq_norm]
          linarith [hsupport]
    _ = f_k n (k + 1) (μ : ℝ)
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (y - x0) +
        M * dist x y := rfl

/-- Helper for Theorem 3.47: the translated hard instance belongs to the strongly convex local
problem class `𝒫_s(x₀, μ, M)`. -/
theorem translated_hard_instance_problemClass
    (x0 : E) (μ M : NNReal) (hμ : 0 < μ) (hM : 0 < M) {k : ℕ} (hk : k + 1 ≤ n) :
    let γ : ℝ := (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))
    let zStar : E := f_k_minimizer n (k + 1) (μ : ℝ) γ
    let xStar : E := x0 + zStar
    let f : E → ℝ := fun x ↦ f_k n (k + 1) (μ : ℝ) γ (x - x0)
    𝒫_s(x0, μ, M) f xStar := by
  dsimp
  have hS0 :
      (fun x ↦
          f_k n (k + 1) (μ : ℝ)
            ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) (x - x0)) ∈
        S0On ((μ : ℝ))
          (Metric.closedBall
            (x0 +
              f_k_minimizer n (k + 1) (μ : ℝ)
                ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))))
            ‖x0 -
              (x0 +
                f_k_minimizer n (k + 1) (μ : ℝ)
                  ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))))‖) := by
    -- Package the translated hard instance into the fixed-modulus strong-convexity owner.
    refine ⟨show 0 < (μ : ℝ) by exact_mod_cast hμ, ?_⟩
    simpa using
      translated_hard_instance_strongConvexOn_closedBall (n := n) x0 μ M hμ hk
  refine ⟨hS0, hM, ?_, ?_⟩
  · -- Reuse the explicit translated minimizer.
    simpa using translated_hard_instance_isMinOn (n := n) x0 μ M hμ hk
  · -- The control-ball Lipschitz estimate comes from bounded translated subgradients.
    simpa using translated_hard_instance_lipschitzOn_closedBall (n := n) x0 μ M hμ hk

/-- Helper for Theorem 3.47: points trapped in the affine prefix subspace cannot decrease the
translated hard-instance value below `0`. -/
theorem translated_hard_instance_nonneg_of_mem_affine_coordinateSubspace
    (x0 x : E) (μ γ : ℝ) {k : ℕ} (hk : k + 1 ≤ n)
    (hμ : 0 ≤ μ) (hγ : 0 ≤ γ)
    (hx : x ∈ AffineSubspace.mk' x0 ℝ^{k,n}) :
    0 ≤ f_k n (k + 1) μ γ (x - x0) := by
  let j : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  have hj_ge : k ≤ j.1 := by
    simp [j]
  have hxj : x j = x0 j :=
    coordinate_eq_start_of_mem_affine_coordinateSubspace (n := n) hx hj_ge
  let iLast : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hcoord_le :
      (x - x0) j ≤ first_k_coordinate_max n (k + 1) (x - x0) := by
    -- The fresh coordinate `k` is one of the coordinates entering the prefix maximum.
    simpa [j, iLast] using
      first_k_coordinate_le_first_k_coordinate_max (n := n) (k := k + 1)
        (Nat.succ_pos k) hk (x - x0) iLast
  have hzero : (x - x0) j = 0 := by
    simp [hxj]
  have hmax_nonneg : 0 ≤ first_k_coordinate_max n (k + 1) (x - x0) := by
    linarith
  -- The quadratic term and the prefix-maximum term are both nonnegative here.
  rw [f_k_def]
  nlinarith [sq_nonneg ‖x - x0‖]

/-- Helper for Theorem 3.47: the translated hard-instance minimum value matches the closed
formula from the source proof. -/
theorem translated_hard_instance_value_gap
    (x0 : E) (μ M : NNReal) (hμ : 0 < μ) {k : ℕ} (hk : k + 1 ≤ n) :
    let γ : ℝ := (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))
    let zStar : E := f_k_minimizer n (k + 1) (μ : ℝ) γ
    let xStar : E := x0 + zStar
    let f : E → ℝ := fun x ↦ f_k n (k + 1) (μ : ℝ) γ (x - x0)
    (-f xStar) ≥
      ((M : ℝ) ^ (2 : ℕ)) /
        ((2 : ℝ) * (μ : ℝ) *
          (((2 : ℝ) + Real.sqrt (((k + 1 : ℕ) : ℝ))) ^ (2 : ℕ))) := by
  dsimp
  have hγ_nonneg :
      0 ≤ (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)) := by
    positivity
  have hvalue :
      f_k n (k + 1) (μ : ℝ)
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))
          (f_k_minimizer n (k + 1) (μ : ℝ)
            ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))) =
        -(((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) ^ (2 : ℕ)) /
          ((2 : ℝ) * (μ : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
    -- Evaluate the untranslated minimizer value using Proposition 3.30.
    simpa using
      f_k_minimizer_value (n := n) (k := k + 1) (μ := (μ : ℝ))
        (γ := (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))
        (Nat.succ_pos k) hk (show 0 < (μ : ℝ) by exact_mod_cast hμ) hγ_nonneg
  have hshift :
      x0 +
          f_k_minimizer n (k + 1) (μ : ℝ)
            ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) -
        x0 =
      f_k_minimizer n (k + 1) (μ : ℝ)
        ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) := by
    abel
  have hclosed :
      -(f_k n (k + 1) (μ : ℝ)
          ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1)))
          (x0 +
            f_k_minimizer n (k + 1) (μ : ℝ)
              ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) -
            x0)) =
        ((M : ℝ) ^ (2 : ℕ)) /
          ((2 : ℝ) * (μ : ℝ) *
            (((2 : ℝ) + Real.sqrt (((k + 1 : ℕ) : ℝ))) ^ (2 : ℕ))) := by
    -- Route correction: avoid unfolding `f_k`; the explicit minimizer-value formula already
    -- gives the exact source constant after one translation rewrite.
    rw [hshift, hvalue]
    have hk_cast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
      norm_num
    rw [hk_cast]
    have hsqrt_sq : Real.sqrt (k + 1) ^ 2 = (k + 1 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    field_simp [show (μ : ℝ) ≠ 0 by exact_mod_cast hμ.ne']
    rw [hsqrt_sq]
  have hclosed_expanded :
      -(↑μ / 2 *
          ‖x0 +
              f_k_minimizer n (k + 1) (μ : ℝ)
                ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) -
            x0‖ ^ 2 +
        ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) *
          first_k_coordinate_max n (k + 1)
            (x0 +
              f_k_minimizer n (k + 1) (μ : ℝ)
                ((M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))) -
              x0)) =
        ((M : ℝ) ^ (2 : ℕ)) /
          ((2 : ℝ) * (μ : ℝ) *
            (((2 : ℝ) + Real.sqrt (((k + 1 : ℕ) : ℝ))) ^ (2 : ℕ))) := by
    simpa [f_k_def] using hclosed
  exact hclosed_expanded.ge

/-- Theorem 3.47: for every `k` with `0 ≤ k ≤ n - 1`, there exists a problem in the strongly
convex class `𝒫_s(x₀, μ, M)` such that every span-based first-order method whose valid
subgradient oracle satisfies `HasCoordinateSupportGrowth` has objective gap at least
`M² / (2 μ (2 + √(k + 1))²)` at its `k`-th iterate. -/
-- Proof sketch: use the Nemirovski--Yudin resisting-oracle hard instance in dimension `k + 1`
-- with parameter `γ = M * √(k + 1) / (2 + √(k + 1))`. The resulting objective is
-- `μ`-strongly convex on the relevant ball around its minimizer, is `M`-Lipschitz on that same
-- ball, and traps the first `k` iterates of every span-based method whose oracle satisfies
-- `HasCoordinateSupportGrowth` in the resisting-oracle subspace, where the hard lower bound
-- remains valid.
theorem exists_stronglyConvexLipschitzProblem_with_span_method_lower_bound
    (x0 : E) (μ M : NNReal)
    (hμ : 0 < μ) (hM : 0 < M) {k : ℕ} (hk : k + 1 ≤ n) :
    ∃ f : E → ℝ,
      ∃ xStar : E,
        𝒫_s(x0, μ, M) f xStar ∧
          ∀ oracle : FirstOrderOracle f,
            HasCoordinateSupportGrowth x0 oracle.subgradient k →
            ∀ xSeq : ℕ → E, SatisfiesLinearSpanCondition x0 oracle.subgradient xSeq k →
              f (xSeq k) - f xStar ≥
                ((M : ℝ) ^ (2 : ℕ)) /
                  ((2 : ℝ) * (μ : ℝ) *
                    (((2 : ℝ) + Real.sqrt (((k + 1 : ℕ) : ℝ))) ^ (2 : ℕ))) := by
  let γ : ℝ := (M : ℝ) * Real.sqrt (k + 1) / ((2 : ℝ) + Real.sqrt (k + 1))
  let zStar : E := f_k_minimizer n (k + 1) (μ : ℝ) γ
  let xStar : E := x0 + zStar
  let f : E → ℝ := fun x ↦ f_k n (k + 1) (μ : ℝ) γ (x - x0)
  have hγ_nonneg : 0 ≤ γ := by
    dsimp [γ]
    positivity
  refine ⟨f, xStar, ?_, ?_⟩
  · -- Package the translated Nemirovski hard instance into the local strong-convexity class.
    simpa [γ, zStar, xStar, f] using
      translated_hard_instance_problemClass (n := n) x0 μ M hμ hM hk
  · intro oracle hgrow xSeq hxSeq
    have hxk :
        xSeq k ∈ AffineSubspace.mk' x0 ℝ^{k,n} :=
      iterates_mem_affine_coordinateSubspace_under_support_growth
        (n := n) hgrow hxSeq k le_rfl
    have hvalue_nonneg : 0 ≤ f (xSeq k) := by
      -- The span/support invariant traps the `k`-th iterate before the fresh coordinate is seen.
      simpa [f] using
        translated_hard_instance_nonneg_of_mem_affine_coordinateSubspace
          (n := n) x0 (xSeq k) (μ : ℝ) γ hk
          (show 0 ≤ (μ : ℝ) by exact_mod_cast hμ.le) hγ_nonneg hxk
    have hopt :
        -f xStar ≥
          ((M : ℝ) ^ (2 : ℕ)) /
            ((2 : ℝ) * (μ : ℝ) *
              (((2 : ℝ) + Real.sqrt (((k + 1 : ℕ) : ℝ))) ^ (2 : ℕ))) := by
      -- The explicit minimizer value is the source lower-bound constant.
      simpa [γ, zStar, xStar, f] using
        translated_hard_instance_value_gap (n := n) x0 μ M hμ hk
    calc
      f (xSeq k) - f xStar ≥ 0 - f xStar := by
        linarith
      _ = -f xStar := by ring
      _ ≥
          ((M : ℝ) ^ (2 : ℕ)) /
            ((2 : ℝ) * (μ : ℝ) *
              (((2 : ℝ) + Real.sqrt (((k + 1 : ℕ) : ℝ))) ^ (2 : ℕ))) := hopt

end EuclideanLowerBound

end
