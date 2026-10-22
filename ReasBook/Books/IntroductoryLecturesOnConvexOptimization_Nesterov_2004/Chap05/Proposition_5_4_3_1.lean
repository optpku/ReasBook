/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_11

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology Filter
open scoped EuclideanOrthant Gradient

noncomputable section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Proposition 5.4.3.1 lies in the Chapter 5 self-concordant barrier / path-following
specialization domain.

Sampled owner declarations in this domain:
* `linearOptimizationProblemWithNonnegativityConstraints` from `Definition_5_4_3_1`, the chapter
  owner for the linear program with equality constraints and nonnegative-orthant basic set;
* `linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet` from
  `Definition_5_4_3_1`, the owner-level strict feasible slice for the same linear program;
* `standardLogarithmicBarrierAmbient` from `Definition_5_4_3_2`, the ambient logarithmic-barrier
  bridge on `ℝⁿ`;
* `pathFollowing_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon` from
  `Theorem_5_3_11`, the canonical stopping theorem.

Best owner abstraction:
* source-facing: the Chapter 5 linear-program owner
  `linearOptimizationProblemWithNonnegativityConstraints A b c` together with its strict feasible
  slice `linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b`;
* core/canonical: the generic stopping theorem for `IsSelfConcordantBarrierOnWith`;
* bridge/view: the ambient logarithmic barrier `standardLogarithmicBarrierAmbient n`.

Primitive data:
* the linear-program owner `linearOptimizationProblemWithNonnegativityConstraints A b c`;
* the strict feasible-set owner
  `linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b`.

Derived API:
* the path-following complexity statement, which is only a specialization of
  `pathFollowing_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon`.

Source/core/bridge triage:
* source-facing: the strict feasible-set owner
  `linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b`;
* core/canonical: the stopping theorem from `Theorem_5_3_11`;
* bridge/view: the ambient barrier `standardLogarithmicBarrierAmbient n`.

The previous version specialized the stopping theorem through a raw objective
`x ↦ ⟪c, x⟫` and a raw feasible-set presentation. This refinement reuses the Chapter 5 linear
program owner and its strict feasible-set owner from `Definition_5_4_3_1`, so the proposition is
organized around the LP owner itself rather than around parallel coordinate-level surface data.
-/

section
local notation "F" => standardLogarithmicBarrierAmbient n

/-
Proposition 5.4.3.1 is the direct Chapter 5 LP specialization of the generic stopping theorem,
with LP owner `linearOptimizationProblemWithNonnegativityConstraints A b c`, strict feasible-set
owner `linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b`, and barrier
`standardLogarithmicBarrierAmbient n`.
-/
theorem
    linearOptimizationProblemWithNonnegativityConstraints_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) (c : Eₙ)
    [IsSelfConcordantBarrierOnWith
      (linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b)
      n
      F]
    {β γ ε : ℝ}
    (xCenter : linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b)
    (hcenter :
      IsMinOn F
        (linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b)
        (xCenter : Eₙ))
    (hxCenterH : (fderiv ℝ (∇ F) (xCenter : Eₙ)).det ≠ 0)
    (xOpt :
      (linearOptimizationProblemWithNonnegativityConstraints A b c).equalityFeasibleSet)
    (hopt :
      ∀ y :
        (linearOptimizationProblemWithNonnegativityConstraints A b c).equalityFeasibleSet,
        linearOptimizationProblemWithNonnegativityConstraints A b c (xOpt : Eₙ) ≤
          linearOptimizationProblemWithNonnegativityConstraints A b c (y : Eₙ))
    (t : ℕ → ℝ) (x : ℕ → Eₙ)
    (mem_dom :
      ∀ k : ℕ, x k ∈ linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b)
    (hessian_nondegenerate : ∀ k : ℕ, (fderiv ℝ (∇ F) (x k)).det ≠ 0)
    (stopIndex : ℕ)
    (hβ_half : β < 1 / 2)
    (hγ : 0 < γ)
    (hcontinue :
      ∀ ⦃k : ℕ⦄, k < stopIndex →
        t k < barrierPathFollowingStoppingThreshold n β ε)
    (hstop : barrierPathFollowingStoppingThreshold n β ε ≤ t stopIndex)
    (hgrowth :
      ∀ k : ℕ, 1 ≤ k →
        (γ * (1 - 2 * β)) /
            ((1 - β) *
                HessianDualLocalNorm.ofDetNeZero F (xCenter : Eₙ)
                  (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xCenter.2)
                  hxCenterH
                  ((InnerProductSpace.toDual ℝ Eₙ) c)) *
            (1 + γ / (β + Real.sqrt (n : ℝ))) ^ (k - 1) ≤
          t k)
    (happrox_stop :
      HessianDualLocalNorm.ofDetNeZero F (x stopIndex)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 (mem_dom stopIndex))
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ Eₙ)
            (t stopIndex • c + ∇ F (x stopIndex))) ≤
        β) :
    stopIndex ≤
        ⌈barrierPathFollowingTerminationBound n β γ ε
          (HessianDualLocalNorm.ofDetNeZero F (xCenter : Eₙ)
            (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xCenter.2) hxCenterH
            ((InnerProductSpace.toDual ℝ Eₙ) c))⌉₊ ∧
      linearOptimizationProblemWithNonnegativityConstraints A b c (x stopIndex) -
          linearOptimizationProblemWithNonnegativityConstraints A b c (xOpt : Eₙ) ≤
        ε := by
  let problem := linearOptimizationProblemWithNonnegativityConstraints A b c
  let strictDom := linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b
  have hxCenter_eq : A.mulVec (xCenter : Eₙ) = b :=
    (mem_linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet_iff A b).1 xCenter.2
      |>.1
  have hxCenter_pos : ∀ i : Fin n, 0 < (xCenter : Eₙ) i := by
    simpa using
      (mem_linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet_iff A b).1
        xCenter.2 |>.2
  have hstrict_subset_eq : strictDom ⊆ problem.equalityFeasibleSet := by
    intro z hz
    rw [mem_linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet_iff] at hz
    rw [mem_linearOptimizationProblemWithNonnegativityConstraints_equalityFeasibleSet_iff]
    refine ⟨?_, hz.1⟩
    intro i
    exact (EuclideanSpace.mem_positiveOrthant_iff.mp hz.2 i).le
  have hclosed_eq : IsClosed problem.equalityFeasibleSet := by
    have hclosed_nonnegativeOrthant : IsClosed (ℝ₊^n : Set Eₙ) := by
      let e : Eₙ ≃ₜ (Fin n → ℝ) := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
      have hnonnegativeOrthant :
          (ℝ₊^n : Set Eₙ) =
            e ⁻¹' Set.pi Set.univ (fun _ : Fin n ↦ Set.Ici (0 : ℝ)) := by
        ext x
        simp [Pi.le_def, e, EuclideanSpace.nonnegativeOrthant]
      rw [hnonnegativeOrthant]
      exact (isClosed_set_pi fun _ _ ↦ isClosed_Ici).preimage e.continuous
    have hclosed_eqConstraint : IsClosed {z : Eₙ | A.toEuclideanLin z = b} := by
      exact
        isClosed_singleton.preimage
          (LinearMap.continuous_of_finiteDimensional A.toEuclideanLin)
    have heq :
        problem.equalityFeasibleSet = (ℝ₊^n : Set Eₙ) ∩ {z : Eₙ | A.toEuclideanLin z = b} := by
      ext z
      rw [PrimalEqualityConstrainedProblem.mem_equalityFeasibleSet_iff]
      simp [problem, linearOptimizationProblemWithNonnegativityConstraints]
    rw [heq]
    exact hclosed_nonnegativeOrthant.inter hclosed_eqConstraint
  have hclosure_subset_eq : closure strictDom ⊆ problem.equalityFeasibleSet :=
    closure_minimal hstrict_subset_eq hclosed_eq
  have heq_subset_closure : problem.equalityFeasibleSet ⊆ closure strictDom := by
    intro z hz
    let path : ℝ → Eₙ := fun s ↦ z + s • ((xCenter : Eₙ) - z)
    have hpath : Filter.Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 z) := by
      have hcont : Continuous path := by
        dsimp [path]
        exact continuous_const.add (continuous_id.smul continuous_const)
      have hpath0 : Filter.Tendsto path (𝓝 (0 : ℝ)) (𝓝 (path 0)) := hcont.continuousAt.tendsto
      simpa [path] using
        (hpath0.mono_left nhdsWithin_le_nhds :
          Filter.Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (path 0)))
    have hz_nonneg_eq :
        (∀ i : Fin n, 0 ≤ z i) ∧ A.mulVec z = b := by
      simpa using
        (mem_linearOptimizationProblemWithNonnegativityConstraints_equalityFeasibleSet_iff A b c).1
          hz
    have hpath_mem :
        ∀ᶠ s in 𝓝[>] (0 : ℝ), path s ∈ strictDom := by
      have hIoo : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 :=
        Ioo_mem_nhdsGT zero_lt_one
      filter_upwards [hIoo] with s hs
      rw [mem_linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet_iff]
      constructor
      · have hs0 : 0 ≤ s := hs.1.le
        have hs1 : s ≤ 1 := hs.2.le
        calc
          A.mulVec (path s)
              = A.mulVec z + s • (A.mulVec ((xCenter : Eₙ) - z)) := by
                  simp [path, Matrix.mulVec_add, Matrix.mulVec_smul]
          _ = b + s • (b - b) := by simp [hz_nonneg_eq.2, hxCenter_eq, Matrix.mulVec_sub]
          _ = b := by simp
      · rw [EuclideanSpace.mem_positiveOrthant_iff]
        intro i
        have hcoord : path s i = (1 - s) * z i + s * (xCenter : Eₙ) i := by
          calc
            path s i = z i + s * ((xCenter : Eₙ) i - z i) := by
              simp [path]
            _ = (1 - s) * z i + s * (xCenter : Eₙ) i := by ring
        rw [hcoord]
        nlinarith [hz_nonneg_eq.1 i, hxCenter_pos i, hs.1, hs.2]
    exact mem_closure_of_tendsto hpath hpath_mem
  let xOptClosure : closure strictDom := ⟨(xOpt : Eₙ), heq_subset_closure xOpt.2⟩
  have hoptClosure :
      ∀ y : closure strictDom, inner ℝ c (xOptClosure : Eₙ) ≤ inner ℝ c (y : Eₙ) := by
    intro y
    exact hopt ⟨y, hclosure_subset_eq y.2⟩
  simpa [linearOptimizationProblemWithNonnegativityConstraints_objective_apply] using
    (pathFollowing_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon
      c xCenter hcenter hxCenterH xOptClosure hoptClosure
      t x mem_dom hessian_nondegenerate stopIndex
      hβ_half hγ hcontinue hstop hgrowth happrox_stop)

end

end
