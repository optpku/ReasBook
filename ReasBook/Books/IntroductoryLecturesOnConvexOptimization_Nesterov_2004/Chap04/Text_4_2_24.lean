/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_7_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient DegreeConditioning FunctionClasses StrongConvexSmooth

noncomputable section

universe u

/- Text 4.2.24 is the Chapter 4 complexity observation for the class
`σ₂(f) > 0`, `L₂(f) < ∞`, `L₃(f) < ∞`: standard optimal first-order methods can reach Newton's
quadratic-convergence region in
`O(√(L₂(f) / σ₂(f)) * log ((L₂(f) * L₃(f)^2 / σ₂(f)^3) * ‖x₀ - xStar‖^2))` iterations.

This file keeps the Chapter 1 tail owner `HasQuadraticConvergenceFrom`, records the source region
`Q_f` from (4.2.60), and packages the logarithmic entry estimate in a natural-index-safe form
with a two-step additive offset. -/

section QuadraticConvergence

variable {E : Type u} [SeminormedAddCommGroup E]

variable {x : ℕ → E} {xStar : E}

/-- A Newton orbit has quadratic convergence to `xStar` from index `k` if it converges to
`xStar` and its error sequence satisfies the Chapter 1 quadratic scalar recurrence from that index
onward. -/
def HasQuadraticConvergenceFrom (x : ℕ → E) (xStar : E) (k : ℕ) : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      Filter.Tendsto x Filter.atTop (nhds xStar) ∧
        HasEventuallySuperlinearErrorBound (fun j ↦ ‖x j - xStar‖) 0 c k

end QuadraticConvergence

section NewtonMethodTail

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace NewtonSystem.Method

/-- If the tail of a Newton method converges quadratically from its initial index, then the
original Newton method converges quadratically from the corresponding shifted index. -/
theorem hasQuadraticConvergenceFrom_of_tail
    {F : E → E} {x0 xStar : E} (method : NewtonSystem.Method F x0) {k : ℕ}
    (h : HasQuadraticConvergenceFrom (method.tail k) xStar 0) :
    HasQuadraticConvergenceFrom method xStar k := by
  rcases h with ⟨c, hc, htendsto, hbound⟩
  refine ⟨c, hc, ?_, Nat.zero_le k, ?_⟩
  · simpa using (Filter.tendsto_add_atTop_iff_nat k).1 htendsto
  · intro j hj
    rcases Nat.exists_eq_add_of_le hj with ⟨n, rfl⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.sub_zero] using
      hbound.bound (Nat.zero_le n)

end NewtonSystem.Method

end NewtonMethodTail

section NewtonQuadraticConvergenceRegion

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} [f ∈ 𝓕₂Lip]

/-- The quadratic-convergence region `Q_f` from (4.2.60), written in zero-safe multiplication
form relative to the chosen minimizer `xStar`. -/
def newtonQuadraticConvergenceRegion
    (f : E → ℝ) [f ∈ 𝓕₂Lip] (xStar : E) : Set E :=
  {x | (2 : ℝ) * L[3](f) ^ (2 : ℕ) * (f x - f xStar) ≤ σ[2](f) ^ (3 : ℕ)}

/-- Membership in `newtonQuadraticConvergenceRegion f xStar` is exactly the source objective-gap
inequality from (4.2.60), written in zero-safe multiplication form. -/
theorem mem_newtonQuadraticConvergenceRegion_iff
    {f : E → ℝ} [f ∈ 𝓕₂Lip] {xStar x : E} :
    x ∈ newtonQuadraticConvergenceRegion f xStar ↔
      (2 : ℝ) * L[3](f) ^ (2 : ℕ) * (f x - f xStar) ≤ σ[2](f) ^ (3 : ℕ) := by
  -- This is just the defining inequality of the source region `Q_f`.
  rfl

end NewtonQuadraticConvergenceRegion

section NewtonQuadraticConvergenceRegionBridge

variable {E : Type u} [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {f : E → ℝ} [f ∈ 𝓕₂Lip] {x0 xStar : E}

/-- Helper for Text 4 2 24: the first iterated derivative is isometric to the Fréchet
derivative. -/
private lemma iteratedFDerivOne_normSub_eq_fderiv_normSub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} (x y : E) :
    ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ = ‖fderiv ℝ g x - fderiv ℝ g y‖ := by
  -- Compare the first iterated derivative with `fderiv` through the canonical currying isometry.
  let e : (E [×1]→L[ℝ] F) ≃ₗᵢ[ℝ] E →L[ℝ] F := continuousMultilinearCurryFin1 ℝ E F
  have hx : e (iteratedFDeriv ℝ 1 g x) = fderiv ℝ g x := by
    ext z
    simp [e]
  have hy : e (iteratedFDeriv ℝ 1 g y) = fderiv ℝ g y := by
    ext z
    simp [e]
  calc
    ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ =
        ‖e (iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y)‖ := by
          simpa using (e.norm_map (iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y)).symm
    _ = ‖fderiv ℝ g x - fderiv ℝ g y‖ := by
          rw [map_sub, hx, hy]

/-- Helper for Text 4 2 24: the second iterated derivative is isometric to the second Fréchet
derivative. -/
private lemma iteratedFDerivTwo_normSub_eq_sndFDeriv_normSub
    {g : E → ℝ} (hg : ContDiff ℝ 2 g) (x y : E) :
    ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ =
      ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ := by
  -- Rewrite the second Taylor coefficient through `iteratedFDeriv`, then curry twice.
  let eEquiv : (E [×2]→L[ℝ] ℝ) ≃ₗᵢ[ℝ] (E [×1]→L[ℝ] E →L[ℝ] ℝ) :=
    continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ
  let e : (E [×2]→L[ℝ] ℝ) →ₗᵢ[ℝ] (E [×1]→L[ℝ] E →L[ℝ] ℝ) := eEquiv.toLinearIsometry
  have hx' : e (iteratedFDeriv ℝ 2 g x) = iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ g z) x := by
    -- The second iterated derivative is the curried first derivative of `fderiv g`.
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp [e, eEquiv]
  have hy' : e (iteratedFDeriv ℝ 2 g y) = iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ g z) y := by
    -- The same currying identity holds at the second base point.
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp [e, eEquiv]
  have hdist :
      dist (iteratedFDeriv ℝ 2 g x) (iteratedFDeriv ℝ 2 g y) =
        dist (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ g z) x)
          (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ g z) y) := by
    simpa [hx', hy'] using (e.dist_map (iteratedFDeriv ℝ 2 g x) (iteratedFDeriv ℝ 2 g y)).symm
  have hiter :
      dist (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ g z) x)
          (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ g z) y) =
        dist (fderiv ℝ (fderiv ℝ g) x) (fderiv ℝ (fderiv ℝ g) y) := by
    let e1 : (E [×1]→L[ℝ] E →L[ℝ] ℝ) ≃ₗᵢ[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
      continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
    have hx1 :
        e1 (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ g z) x) = fderiv ℝ (fderiv ℝ g) x := by
      ext z
      simp [e1]
    have hy1 :
        e1 (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ g z) y) = fderiv ℝ (fderiv ℝ g) y := by
      ext z
      simp [e1]
    simpa [hx1, hy1] using
      (e1.dist_map (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ g z) x)
        (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ g z) y)).symm
  calc
    ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ =
        dist (iteratedFDeriv ℝ 2 g x) (iteratedFDeriv ℝ 2 g y) := by
          rw [dist_eq_norm]
    _ = dist (fderiv ℝ (fderiv ℝ g) x) (fderiv ℝ (fderiv ℝ g) y) := hdist.trans hiter
    _ = ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ := by
          exact dist_eq_norm (fderiv ℝ (fderiv ℝ g) x) (fderiv ℝ (fderiv ℝ g) y)

/-- Helper for Text 4 2 24: any degree-two uniform-convexity witness yields the corresponding
whole-space strong-convexity owner. -/
private lemma strongConvexOn_of_uniformConvexDegreeTwo
    {g : E → ℝ} {σ : ℝ}
    (huniform : UniformConvexOn Set.univ (uniformConvexPowerModulus σ (2 : ℝ)) g) :
    StrongConvexOn Set.univ σ g := by
  -- Route correction: use the Chapter 4 modulus directly and rewrite it into the mathlib
  -- strong-convexity modulus `(σ / 2) * r^2`.
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change
    g (a • x + b • y) ≤
      a * g x + b * g y - a * b * (σ / 2 * ‖x - y‖ ^ (2 : ℕ))
  have h :=
    huniform.2 (by simp : x ∈ Set.univ) (by simp : y ∈ Set.univ) ha hb hab
  have hpow : ‖x - y‖.rpow (2 : ℝ) = ‖x - y‖ ^ (2 : ℕ) := by
    simpa using (Real.rpow_two ‖x - y‖)
  rw [uniformConvexPowerModulus, hpow] at h
  ring_nf at h ⊢
  exact h

/-- Helper for Text 4 2 24: membership in `𝓕₂Lip` supplies a concrete Hessian-Lipschitz witness
for `f`, even before promoting that witness to the canonical constant `L[3](f)`. -/
lemma exists_memC22_of_f2Lip {f : E → ℝ} [f ∈ 𝓕₂Lip] :
    ∃ L : NNReal, f ∈ C22[L] := by
  rcases (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 3 f).exists_mem with
    ⟨L, hL⟩
  let hcontDiffTwo : ContDiff ℝ 2 f :=
    by simpa using (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 3 f).contDiff
  refine ⟨L, hcontDiffTwo, ?_⟩
  -- Reuse the concrete degree-three witness directly to build the Chapter 4 owner.
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  by_cases hxy : x = y
  · subst hxy
    have hleft : ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) x‖ = 0 := by
      rw [sub_self]
      exact ContinuousLinearMap.opNorm_zero
    have hright : (L : ℝ) * ‖x - x‖ = 0 := by simp
    rw [hleft, hright]
  · have hraw :
        ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ (L : ℝ) * ‖x - y‖ :=
      @HasIteratedFDerivLipschitzConstantOfDegree.norm_sub_le E _ _ L 3 f hL x y
    rw [← iteratedFDerivTwo_normSub_eq_sndFDeriv_normSub hcontDiffTwo x y]
    exact hraw

/-- Helper for Text 4 2 24: membership in `𝓕₂Lip` supplies concrete strong-convexity and
gradient-Lipschitz witnesses for `f`, even before promoting them to the canonical constants
`σ[2](f)` and `L[2](f)`. -/
lemma exists_strongConvexSmoothObjective_of_f2Lip {f : E → ℝ} [f ∈ 𝓕₂Lip] :
    ∃ σ > 0, ∃ L : NNReal, IsStrongConvexSmoothObjective σ L f := by
  rcases (inferInstance : HasUniformConvexityParameterOfDegree 2 f).exists_mem with
    ⟨σ, hσ, huniform⟩
  rcases (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 2 f).exists_mem with
    ⟨L, hL⟩
  let hcontDiffOne : ContDiff ℝ 1 f :=
    by simpa using (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 2 f).contDiff
  refine ⟨σ, hσ, L, ?_⟩
  refine ⟨hσ, hcontDiffOne, strongConvexOn_of_uniformConvexDegreeTwo huniform, ?_⟩
  intro x y
  by_cases hxy : x = y
  · subst hxy
    simp
  · have hx : (InnerProductSpace.toDual ℝ E) (∇ f x) = fderiv ℝ f x :=
        ((hcontDiffOne.differentiable_one x).hasGradientAt.hasFDerivAt.fderiv).symm
    have hy : (InnerProductSpace.toDual ℝ E) (∇ f y) = fderiv ℝ f y :=
        ((hcontDiffOne.differentiable_one y).hasGradientAt.hasFDerivAt.fderiv).symm
    have hraw :
        ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ ≤ (L : ℝ) * ‖x - y‖ :=
      @HasIteratedFDerivLipschitzConstantOfDegree.norm_sub_le E _ _ L 2 f hL x y
    have hfderiv :
        ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
      rw [← iteratedFDerivOne_normSub_eq_fderiv_normSub x y]
      exact hraw
    have hgradEq : ‖∇ f x - ∇ f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
      calc
        ‖∇ f x - ∇ f y‖ = ‖(InnerProductSpace.toDual ℝ E) (∇ f x - ∇ f y)‖ := by
          simpa using ((InnerProductSpace.toDual ℝ E).norm_map (∇ f x - ∇ f y)).symm
        _ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
          rw [map_sub, hx, hy]
    simpa [hgradEq] using hfderiv

/-- Helper for Text 4 2 24: the canonical constant `L[2](f)` controls the first iterated
derivative exactly. -/
private lemma iteratedFDerivOne_norm_sub_le_canonical
    {g : E → ℝ} [HasIteratedFDerivLipschitzConstantOfDegree 2 g]
    (x y : E) :
    ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ ≤ (L[2](g) : ℝ) * ‖x - y‖ := by
  let S : Set NNReal := {L : NNReal | g ∈ 𝒞^{1,1}_{L}(Set.univ)}
  by_cases hxy : x = y
  · -- On the diagonal the estimate is immediate.
    subst hxy
    simp
  · -- Off the diagonal, compare the exact slope ratio against every admissible witness.
    have hdist_pos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    let r : NNReal :=
      ⟨‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ / ‖x - y‖, by positivity⟩
    have hr : r ≤ L[2](g) := by
      change r ≤ sInf S
      refine le_csInf ?_ ?_
      · rcases
          (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 2 g).exists_mem with
          ⟨L, hL⟩
        exact ⟨L, hL⟩
      · intro L hL
        have hL' : g ∈ 𝒞^{1,1}_{L}(Set.univ) := by
          simpa [S] using hL
        have hbound :
            ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ ≤ (L : ℝ) * ‖x - y‖ :=
          @HasIteratedFDerivLipschitzConstantOfDegree.norm_sub_le E _ _ L 2 g hL' x y
        exact_mod_cast (show
            ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ / ‖x - y‖ ≤ (L : ℝ) by
          exact (div_le_iff₀ hdist_pos).2 hbound)
    exact
      (div_le_iff₀ hdist_pos).mp <| by
        simpa [r] using (show (r : ℝ) ≤ (L[2](g) : ℝ) from by exact_mod_cast hr)

/-- Helper for Text 4 2 24: the canonical constant `L[3](f)` controls the second iterated
derivative exactly. -/
private lemma iteratedFDerivTwo_norm_sub_le_canonical
    {g : E → ℝ} [HasIteratedFDerivLipschitzConstantOfDegree 3 g]
    (x y : E) :
    ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ (L[3](g) : ℝ) * ‖x - y‖ := by
  let S : Set NNReal := {L : NNReal | g ∈ 𝒞^{2,2}_{L}(Set.univ)}
  by_cases hxy : x = y
  · -- On the diagonal the estimate is immediate.
    subst hxy
    simp
  · -- Off the diagonal, compare the exact slope ratio against every admissible witness.
    have hdist_pos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    let r : NNReal :=
      ⟨‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ / ‖x - y‖, by positivity⟩
    have hr : r ≤ L[3](g) := by
      change r ≤ sInf S
      refine le_csInf ?_ ?_
      · rcases
          (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 3 g).exists_mem with
          ⟨L, hL⟩
        exact ⟨L, hL⟩
      · intro L hL
        have hL' : g ∈ 𝒞^{2,2}_{L}(Set.univ) := by
          simpa [S] using hL
        have hbound :
            ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ (L : ℝ) * ‖x - y‖ :=
          @HasIteratedFDerivLipschitzConstantOfDegree.norm_sub_le E _ _ L 3 g hL' x y
        exact_mod_cast (show
            ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ / ‖x - y‖ ≤ (L : ℝ) by
          exact (div_le_iff₀ hdist_pos).2 hbound)
    exact
      (div_le_iff₀ hdist_pos).mp <| by
        simpa [r] using (show (r : ℝ) ≤ (L[3](g) : ℝ) from by exact_mod_cast hr)

/-- Helper for Text 4 2 24: the canonical degree-two parameter `σ[2](f)` already satisfies the
pointwise Hessian quadratic-form lower bound. -/
private lemma sigma2HessianQuadraticFormLowerBound
    {g : E → ℝ} [g ∈ 𝓕₂Lip] (x u : E) :
    σ[2](g) * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ (hessian g x u) u := by
  let S : Set ℝ := {σ : ℝ |
    0 < σ ∧ UniformConvexOn Set.univ (uniformConvexPowerModulus σ (2 : ℝ)) g}
  by_cases hu : u = 0
  · -- The zero direction makes the quadratic-form bound tautological.
    simp [hu]
  · have hσ_pos : 0 < σ[2](g) :=
      IsInFunctionClassF2Lip.sigma_pos (inferInstance : g ∈ 𝓕₂Lip)
    have hcontDiffTwo : ContDiff ℝ 2 g := by
      simpa using
        (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 3 g).contDiff
    have hu_sq_pos : 0 < ‖u‖ ^ (2 : ℕ) := by
      positivity
    have hratio :
        σ[2](g) ≤ inner ℝ (hessian g x u) u / ‖u‖ ^ (2 : ℕ) := by
      change sSup S ≤ inner ℝ (hessian g x u) u / ‖u‖ ^ (2 : ℕ)
      have hnonempty : Set.Nonempty S := HasUniformConvexityParameterOfDegree.nonempty
      refine csSup_le hnonempty ?_
      intro σ hσ
      have hstrong : StrongConvexOn Set.univ σ g :=
        strongConvexOn_of_uniformConvexDegreeTwo hσ.2
      have hbound :
          σ • (1 : E →L[ℝ] E) ≤ hessian g x := by
        -- Convert the witness-level degree-two modulus into the corresponding Hessian lower bound.
        have hiff :=
          (strongConvexOn_iff_hessian_lower_bound
            hσ.1 convex_univ
            (by simp)
            hcontDiffTwo.continuous.continuousOn
            (by simpa using hcontDiffTwo.contDiffOn)).1 hstrong
        simpa using hiff x (by simp)
      have hquad :
          σ * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ (hessian g x u) u := by
        exact
          (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
            hσ.1
            (by simpa using hcontDiffTwo.contDiffOn)
            (by simp : x ∈ interior (Set.univ : Set E))).1 hbound u
      exact (le_div_iff₀ hu_sq_pos).2 hquad
    -- Multiply the supremum bound back by `‖u‖²` to recover the desired quadratic form estimate.
    exact (le_div_iff₀ hu_sq_pos).1 hratio

/-- Helper for Text 4 2 24: the canonical degree-two parameter `σ[2](f)` gives the exact
whole-space Hessian Loewner lower bound. -/
private lemma sigma2HessianLowerBound
    {g : E → ℝ} [g ∈ 𝓕₂Lip] (x : E) :
    σ[2](g) • (1 : E →L[ℝ] E) ≤ hessian g x := by
  have hσ_pos : 0 < σ[2](g) :=
    IsInFunctionClassF2Lip.sigma_pos (inferInstance : g ∈ 𝓕₂Lip)
  have hcontDiffTwo : ContDiff ℝ 2 g := by
    simpa using
      (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 3 g).contDiff
  -- Repackage the pointwise quadratic-form inequality as the operator Loewner bound.
  exact
    (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
      hσ_pos
      (by simpa using hcontDiffTwo.contDiffOn)
      (by simp : x ∈ interior (Set.univ : Set E))).2
      (sigma2HessianQuadraticFormLowerBound x)

/-- Helper for Text 4 2 24: the canonical degree-two parameter `σ[2](f)` already satisfies the
global strong-convexity owner. -/
private lemma f2Lip_strongConvexOn_sigma2 {g : E → ℝ} [g ∈ 𝓕₂Lip] :
    StrongConvexOn Set.univ (σ[2](g)) g := by
  have hσ_pos : 0 < σ[2](g) :=
    IsInFunctionClassF2Lip.sigma_pos (inferInstance : g ∈ 𝓕₂Lip)
  have hcontDiffTwo : ContDiff ℝ 2 g := by
    simpa using
      (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 3 g).contDiff
  -- Route correction: first prove the exact Hessian lower bound at the canonical `σ[2](g)`,
  -- then transport it back to whole-space strong convexity.
  refine
    (strongConvexOn_iff_hessian_lower_bound
      hσ_pos convex_univ
      (by simp)
      hcontDiffTwo.continuous.continuousOn
      (by simpa using hcontDiffTwo.contDiffOn)).2 ?_
  intro x hx
  simpa using sigma2HessianLowerBound x

/-- Helper for Text 4 2 24: membership in `𝓕₂Lip` already yields the exact Chapter 2 owner
`𝓢[σ[2](f), L[2](f)]¹¹`. -/
private lemma f2Lip_memS11 {g : E → ℝ} [g ∈ 𝓕₂Lip] :
    g ∈ 𝓢[σ[2](g), L[2](g)]¹¹ := by
  have hσ_pos : 0 < σ[2](g) :=
    IsInFunctionClassF2Lip.sigma_pos (inferInstance : g ∈ 𝓕₂Lip)
  have hcontDiffOne : ContDiff ℝ 1 g := by
    simpa using
      (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 2 g).contDiff
  refine mem_S11_iff.mpr ⟨hσ_pos, hcontDiffOne, f2Lip_strongConvexOn_sigma2, ?_⟩
  intro x y
  -- Promote the canonical Taylor-class owner to the gradient-Lipschitz owner at `L[2](g)`.
  have hfderiv :
      ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ (L[2](g) : ℝ) * ‖x - y‖ := by
    rw [← iteratedFDerivOne_normSub_eq_fderiv_normSub x y]
    simpa using iteratedFDerivOne_norm_sub_le_canonical x y
  have hx :
      (InnerProductSpace.toDual ℝ E) (∇ g x) = fderiv ℝ g x :=
    ((hcontDiffOne.differentiable_one x).hasGradientAt.hasFDerivAt.fderiv).symm
  have hy :
      (InnerProductSpace.toDual ℝ E) (∇ g y) = fderiv ℝ g y :=
    ((hcontDiffOne.differentiable_one y).hasGradientAt.hasFDerivAt.fderiv).symm
  have hgradEq : ‖∇ g x - ∇ g y‖ = ‖fderiv ℝ g x - fderiv ℝ g y‖ := by
    calc
      ‖∇ g x - ∇ g y‖ = ‖(InnerProductSpace.toDual ℝ E) (∇ g x - ∇ g y)‖ := by
        simpa using ((InnerProductSpace.toDual ℝ E).norm_map (∇ g x - ∇ g y)).symm
      _ = ‖fderiv ℝ g x - fderiv ℝ g y‖ := by
        rw [map_sub, hx, hy]
  simpa [hgradEq] using hfderiv

/-- Helper for Text 4 2 24: membership in `𝓕₂Lip` already yields the exact Chapter 1 owner
`C22[L[3](f)]`. -/
private lemma f2Lip_memC22 {g : E → ℝ} [g ∈ 𝓕₂Lip] :
    g ∈ C22[L[3](g)] := by
  have hcontDiffTwo : ContDiff ℝ 2 g := by
    simpa using
      (inferInstance : HasIteratedFDerivLipschitzConstantOfDegree 3 g).contDiff
  refine ⟨hcontDiffTwo, ?_⟩
  -- The exact `C22` owner is just the `p = 3` canonical Taylor-class owner in Hessian form.
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  rw [← iteratedFDerivTwo_normSub_eq_sndFDeriv_normSub hcontDiffTwo x y]
  simpa using iteratedFDerivTwo_norm_sub_le_canonical x y

/-- Helper for Text 4 2 24: a whole-space strong-convexity lower bound controls the Hessian
operator from below in norm. -/
private lemma hessian_apply_norm_ge_sigma_mul_norm
    {σ : ℝ} {g : E → ℝ}
    (hg : StrongConvexOn Set.univ σ g) (hσ : 0 < σ)
    (hgC2 : ContDiff ℝ 2 g) (x u : E) :
    σ * ‖u‖ ≤ ‖(fderiv ℝ (∇ g) x) u‖ := by
  have hUniv_nonempty : (interior (Set.univ : Set E)).Nonempty := by
    simpa using (Set.nonempty_univ : Set.Nonempty (Set.univ : Set E))
  have hcont : ContinuousOn g (Set.univ : Set E) := hgC2.continuous.continuousOn
  have hC2 : ContDiffOn ℝ 2 g (interior (Set.univ : Set E)) := by
    simpa using hgC2.contDiffOn
  have hbound : σ • (1 : E →L[ℝ] E) ≤ hessian g x := by
    -- Specialize the Chapter 2 Hessian bridge to the ambient whole space.
    have hiff :=
      (strongConvexOn_iff_hessian_lower_bound
        hσ convex_univ hUniv_nonempty hcont hC2).1 hg
    simpa using hiff x (by simp)
  have hquad :
      σ * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ (hessian g x u) u := by
    exact
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hσ hC2 (by simp : x ∈ interior (Set.univ : Set E))).1 hbound u
  by_cases hu : u = 0
  · -- The zero vector saturates the lower bound.
    simp [hu]
  · -- Combine the quadratic-form lower bound with Cauchy-Schwarz and cancel `‖u‖`.
    have hinner_le : inner ℝ (hessian g x u) u ≤ ‖hessian g x u‖ * ‖u‖ := by
      exact le_trans (le_abs_self _) <| by
        simpa [real_inner_comm] using abs_real_inner_le_norm (hessian g x u) u
    have hmul : σ * ‖u‖ ^ (2 : ℕ) ≤ ‖hessian g x u‖ * ‖u‖ := le_trans hquad hinner_le
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hmul' : σ * ‖u‖ * ‖u‖ ≤ ‖hessian g x u‖ * ‖u‖ := by
      simpa [pow_two, mul_assoc] using hmul
    have hdiv := (mul_le_mul_iff_of_pos_right hu_norm_pos).mp hmul'
    simpa [hessian] using hdiv

/-- Helper for Text 4 2 24: the inverse Hessian at any admissible Newton point is globally
bounded by `σ⁻¹` under whole-space `σ`-strong convexity. -/
private lemma inverseFDerivGradient_apply_le_inv_sigma
    {σ : ℝ} {g : E → ℝ}
    (hg : StrongConvexOn Set.univ σ g) (hσ : 0 < σ)
    (hgC2 : ContDiff ℝ 2 g)
    (p : NewtonSystem.AdmissiblePoint (∇ g)) (v : E) :
    ‖(((fderiv ℝ (∇ g) (p : E)).toContinuousLinearEquivOfDetNeZero p.property).symm v)‖ ≤
      (1 / σ) * ‖v‖ := by
  let u :=
    (((fderiv ℝ (∇ g) (p : E)).toContinuousLinearEquivOfDetNeZero p.property).symm v)
  have hbound :
      σ * ‖u‖ ≤ ‖(fderiv ℝ (∇ g) (p : E)) u‖ :=
    hessian_apply_norm_ge_sigma_mul_norm hg hσ hgC2 (p : E) u
  have happly :
      (fderiv ℝ (∇ g) (p : E)) u = v := by
    exact
      (fderiv ℝ (∇ g) (p : E)).toContinuousLinearEquivOfDetNeZero p.property |>.apply_symm_apply v
  have hdiv : ‖u‖ ≤ ‖v‖ / σ := by
    refine (le_div_iff₀ hσ).2 ?_
    simpa [u, happly, mul_comm, mul_left_comm, mul_assoc] using hbound
  simpa [u, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Helper for Text 4 2 24: the canonical Newton step satisfies the quadratic position-error
recurrence at the exact canonical constants. -/
private lemma newtonStepErrorLeQuadratic
    {g : E → ℝ} [g ∈ 𝓕₂Lip] {xStar : E}
    (hxStar : IsMinOn g Set.univ xStar)
    (p : NewtonSystem.AdmissiblePoint (∇ g)) :
    ‖NewtonSystem.step (∇ g) p - xStar‖ ≤
      ((L[3](g) : ℝ) / (2 * σ[2](g))) * ‖(p : E) - xStar‖ ^ (2 : ℕ) := by
  let A : E →L[ℝ] E := hessian g (p : E)
  let Ainv : E →L[ℝ] E :=
    (((fderiv ℝ (∇ g) (p : E)).toContinuousLinearEquivOfDetNeZero p.property).symm :
      E →L[ℝ] E)
  let e : E := (p : E) - xStar
  have hσ_pos : 0 < σ[2](g) :=
    IsInFunctionClassF2Lip.sigma_pos (inferInstance : g ∈ 𝓕₂Lip)
  have hgS11 : g ∈ 𝓢[σ[2](g), L[2](g)]¹¹ := f2Lip_memS11
  have hgC22 : g ∈ C22[L[3](g)] := f2Lip_memC22
  have hgStrong : StrongConvexOn Set.univ (σ[2](g)) g := f2Lip_strongConvexOn_sigma2
  have hgrad0 : ∇ g xStar = 0 := by
    exact (mem_S11_iff.mp hgS11).gradient_eq_zero_of_isMinOn hxStar
  have hstep_eq :
      NewtonSystem.step (∇ g) p - xStar = Ainv (A e - ∇ g (p : E)) := by
    -- Rewrite the Newton correction as inverse Hessian applied to the gradient Taylor remainder.
    calc
      NewtonSystem.step (∇ g) p - xStar = ((p : E) - Ainv (∇ g (p : E))) - xStar := by
        simp [NewtonSystem.step_def, Ainv]
      _ = e - Ainv (∇ g (p : E)) := by
        simp [e, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = Ainv (A e) - Ainv (∇ g (p : E)) := by
        rw [show Ainv (A e) = e by
          simpa [A, Ainv, hessian] using
            (ContinuousLinearEquiv.symm_apply_apply
              ((fderiv ℝ (∇ g) (p : E)).toContinuousLinearEquivOfDetNeZero p.property) e)]
      _ = Ainv (A e - ∇ g (p : E)) := by
        simp
  have hremainder_raw :
      ‖A e - ∇ g (p : E)‖ ≤ ((L[3](g) : ℝ) / 2) * ‖xStar - (p : E)‖ ^ (2 : ℕ) := by
    -- The Chapter 1 gradient Taylor remainder controls the Newton linearization defect.
    simpa [A, e, hgrad0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (HasLipschitzContinuousHessian.gradient_deviation_le hgC22 (p : E) xStar)
  have hremainder :
      ‖A e - ∇ g (p : E)‖ ≤ ((L[3](g) : ℝ) / 2) * ‖e‖ ^ (2 : ℕ) := by
    calc
      ‖A e - ∇ g (p : E)‖ ≤ ((L[3](g) : ℝ) / 2) * ‖xStar - (p : E)‖ ^ (2 : ℕ) :=
        hremainder_raw
      _ = ((L[3](g) : ℝ) / 2) * ‖e‖ ^ (2 : ℕ) := by
        rw [norm_sub_rev]
  have hAinv :
      ∀ v : E, ‖Ainv v‖ ≤ (1 / σ[2](g)) * ‖v‖ := by
    intro v
    -- The exact `σ[2](g)` Hessian lower bound gives a global inverse bound at every admissible point.
    simpa [Ainv] using
      inverseFDerivGradient_apply_le_inv_sigma
        hgStrong hσ_pos hgC22.contDiff p v
  have hσ_ne : σ[2](g) ≠ 0 := ne_of_gt hσ_pos
  calc
    ‖NewtonSystem.step (∇ g) p - xStar‖ = ‖Ainv (A e - ∇ g (p : E))‖ := by
      rw [hstep_eq]
    _ ≤ (1 / σ[2](g)) * ‖A e - ∇ g (p : E)‖ := hAinv _
    _ ≤ (1 / σ[2](g)) * (((L[3](g) : ℝ) / 2) * ‖e‖ ^ (2 : ℕ)) := by
      gcongr
    _ = ((L[3](g) : ℝ) / (2 * σ[2](g))) * ‖e‖ ^ (2 : ℕ) := by
      field_simp [hσ_ne]
    _ = ((L[3](g) : ℝ) / (2 * σ[2](g))) * ‖(p : E) - xStar‖ ^ (2 : ℕ) := by
      simp [e]

/-- If a Newton iterate lies in the source region `Q_f`, then Newton's method converges
quadratically from that index onward. -/
theorem hasQuadraticConvergenceFrom_of_mem_newtonQuadraticConvergenceRegion
    (hxStar : IsMinOn f Set.univ xStar)
    (method : NewtonSystem.Method (∇ f) x0)
    {k : ℕ}
    (hk : method k ∈ newtonQuadraticConvergenceRegion f xStar) :
    HasQuadraticConvergenceFrom method xStar k := by
  let tail := method.tail k
  let r : ℕ → ℝ := fun j ↦ ‖tail j - xStar‖
  have hσ_pos : 0 < σ[2](f) :=
    IsInFunctionClassF2Lip.sigma_pos (inferInstance : f ∈ 𝓕₂Lip)
  have hr_nonneg : ∀ j : ℕ, 0 ≤ r j := by
    intro j
    exact norm_nonneg _
  have finish :
      ∀ {c : ℝ},
        0 < c →
        (∀ j : ℕ, r (j + 1) ≤ c * (r j) ^ (2 : ℕ)) →
        c * r 0 ≤ (1 / 2 : ℝ) →
        HasQuadraticConvergenceFrom method xStar k := by
    intro c hc hquad hbootstrap
    have hsuperlinear : HasEventuallySuperlinearErrorBound r 0 c 0 :=
      HasEventuallySuperlinearErrorBound.of_quadratic_bound hquad
    have hbootstrap_all : ∀ j : ℕ, c * r j ≤ (1 / 2 : ℝ) := by
      intro j
      induction j with
      | zero =>
          exact hbootstrap
      | succ j ih =>
          calc
            c * r (j + 1) ≤ c * (c * (r j) ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left (hquad j) hc.le
            _ = (c * r j) ^ (2 : ℕ) := by
              ring
            _ ≤ ((1 / 2 : ℝ)) ^ (2 : ℕ) := by
              gcongr
            _ ≤ (1 / 2 : ℝ) := by
              norm_num
    have hlinear : ∀ j : ℕ, r (j + 1) ≤ (1 / 2 : ℝ) * r j := by
      intro j
      exact
        HasEventuallySuperlinearErrorBound.linear_bound_of_mul_le_half
          hsuperlinear (hr_nonneg j) (hbootstrap_all j)
    have hgeom : HasGeometricRateOfConvergence r (1 / 2 : ℝ) (r 0) := by
      refine HasGeometricRateOfConvergence.of_step_bound (by norm_num) le_rfl ?_
      intro j
      simpa using (show r (j + 1) ≤ (1 - (1 / 2 : ℝ)) * r j by
        norm_num
        exact hlinear j)
    have htendsto_r : Filter.Tendsto r Filter.atTop (nhds 0) := by
      exact
        HasGeometricRateOfConvergence.tendsto_zero hgeom hr_nonneg (hr_nonneg 0)
          (by norm_num) (by norm_num)
    have htendsto_tail : Filter.Tendsto tail Filter.atTop (nhds xStar) := by
      -- Convergence of the error norm is exactly convergence of the tail to the minimizer.
      exact (tendsto_iff_norm_sub_tendsto_zero).2 <| by simpa [r] using htendsto_r
    -- Package the tail estimate and shift it back to the original Newton orbit.
    exact
      NewtonSystem.Method.hasQuadraticConvergenceFrom_of_tail method
        ⟨c, hc, htendsto_tail, hsuperlinear⟩
  by_cases hLzero : (L[3](f) : ℝ) = 0
  · let c : ℝ := 1 / (2 * (r 0 + 1))
    have hc : 0 < c := by
      positivity
    have hquad : ∀ j : ℕ, r (j + 1) ≤ c * (r j) ^ (2 : ℕ) := by
      intro j
      have hstep := newtonStepErrorLeQuadratic hxStar (tail.x j)
      have hzero : r (j + 1) ≤ 0 := by
        simpa [r, tail.succ_eq, hLzero] using hstep
      exact hzero.trans (by positivity)
    have hbootstrap : c * r 0 ≤ (1 / 2 : ℝ) := by
      have hden_pos : 0 < 2 * (r 0 + 1) := by
        nlinarith [hr_nonneg 0]
      dsimp [c]
      rw [show (1 / (2 * (r 0 + 1))) * r 0 = r 0 / (2 * (r 0 + 1)) by ring]
      refine (div_le_iff₀ hden_pos).2 ?_
      nlinarith [hr_nonneg 0]
    exact finish hc hquad hbootstrap
  · let c : ℝ := ((L[3](f) : ℝ) / (2 * σ[2](f)))
    have hL_pos : 0 < (L[3](f) : ℝ) := by
      have hL_nonneg : 0 ≤ (L[3](f) : ℝ) := by positivity
      exact lt_of_le_of_ne hL_nonneg (Ne.symm hLzero)
    have hc : 0 < c := by
      positivity
    have hquad : ∀ j : ℕ, r (j + 1) ≤ c * (r j) ^ (2 : ℕ) := by
      intro j
      -- Each shifted Newton step satisfies the canonical quadratic error estimate.
      simpa [r, c, tail.succ_eq] using
        newtonStepErrorLeQuadratic hxStar (tail.x j)
    have hbootstrap : c * r 0 ≤ (1 / 2 : ℝ) := by
      have hk_gap :
          (2 : ℝ) * L[3](f) ^ (2 : ℕ) * (f (tail 0) - f xStar) ≤ σ[2](f) ^ (3 : ℕ) := by
        simpa [tail] using hk
      have hgrowth :
          (σ[2](f) / 2) * ‖tail 0 - xStar‖ ^ (2 : ℕ) ≤ f (tail 0) - f xStar := by
        have hf' : IsStrongConvexSmoothObjective (σ[2](f)) L[2](f) f :=
          mem_S11_iff.mp f2Lip_memS11
        have hgrad0 : ∇ f xStar = 0 := hf'.gradient_eq_zero_of_isMinOn hxStar
        have hquadGrowth := hf'.lower_tangent_quadratic xStar (tail 0)
        have hquadGrowth' :
            f (tail 0) ≥ f xStar + (σ[2](f) / 2) * ‖tail 0 - xStar‖ ^ (2 : ℕ) := by
          simpa [hgrad0] using hquadGrowth
        linarith [hquadGrowth']
      have hLr : (L[3](f) : ℝ) * r 0 ≤ σ[2](f) := by
        have hsq : (((L[3](f) : ℝ) * r 0) : ℝ) ^ (2 : ℕ) ≤ σ[2](f) ^ (2 : ℕ) := by
          have hL_nonneg : 0 ≤ (L[3](f) : ℝ) := by positivity
          have hr0_nonneg : 0 ≤ r 0 := hr_nonneg 0
          have hgrowth' : (σ[2](f) / 2) * (r 0) ^ (2 : ℕ) ≤ f (tail 0) - f xStar := by
            simpa [r] using hgrowth
          nlinarith [hk_gap, hgrowth', hσ_pos, hL_nonneg, hr0_nonneg]
        have hLr_nonneg : 0 ≤ (L[3](f) : ℝ) * r 0 := by
          positivity
        nlinarith [hsq, hLr_nonneg, hσ_pos]
      have hden_pos : 0 < 2 * σ[2](f) := by positivity
      dsimp [c]
      rw [show ((L[3](f) : ℝ) / (2 * σ[2](f))) * r 0 =
          ((L[3](f) : ℝ) * r 0) / (2 * σ[2](f)) by ring]
      refine (div_le_iff₀ hden_pos).2 ?_
      nlinarith [hLr]
    exact finish hc hquad hbootstrap

end NewtonQuadraticConvergenceRegionBridge

section NewtonQuadraticConvergenceEntryBound

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} [f ∈ 𝓕₂Lip]

-- Semantic recall note: `lean_leansearch` did not surface a reusable owner for this natural-index
-- bridge, so this file follows a larger additive-offset pattern from `Theorem_5_3_11` rather than
-- the
-- least-entry `max 0` pattern used in `Text_4_2_13`.
/-- An index-safe form of the logarithmic entry bound from (4.2.79). The logarithm keeps the
initial-distance factor inside it, exactly as in the source estimate, and the additive `2`
prevents the near-threshold regime `R → 1⁺` from forcing an unjustified one-step entry claim. -/
def newtonQuadraticConvergenceEntryBound
    (f : E → ℝ) [f ∈ 𝓕₂Lip] (x0 xStar : E) (C : ℝ) : ℝ :=
  2 +
    max 0
      (C *
        (Real.sqrt (L[2](f) / σ[2](f)) *
          Real.log
            ((L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
              σ[2](f) ^ (3 : ℕ))))

/-- The entry-time bound from Text 4.2.24 is nonnegative by construction. -/
theorem newtonQuadraticConvergenceEntryBound_nonneg
    (f : E → ℝ) [f ∈ 𝓕₂Lip] (x0 xStar : E) (C : ℝ) :
    0 ≤ newtonQuadraticConvergenceEntryBound f x0 xStar C := by
  -- The additive offset `2` and the `max 0 _` term are both nonnegative.
  dsimp [newtonQuadraticConvergenceEntryBound]
  positivity

end NewtonQuadraticConvergenceEntryBound

section NewtonQuadraticConvergenceEntry

variable {E : Type u} [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {f : E → ℝ} [f ∈ 𝓕₂Lip]
variable {x0 : E}

/-- Helper for Text 4 2 24: if the canonical ratio
`L[2](f) * L[3](f)^2 * ‖x0 - xStar‖^2 / σ[2](f)^3` is at most `1`, then the initial point already
lies in the Newton quadratic-convergence region. -/
private lemma mem_newtonQuadraticConvergenceRegion_of_ratio_le_one
    {f : E → ℝ} [f ∈ 𝓕₂Lip] {x0 xStar : E}
    (hxStar : IsMinOn f Set.univ xStar)
    (hratio :
      L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤ σ[2](f) ^ (3 : ℕ)) :
    x0 ∈ newtonQuadraticConvergenceRegion f xStar := by
  have hf' : IsStrongConvexSmoothObjective (σ[2](f)) L[2](f) f :=
    mem_S11_iff.mp f2Lip_memS11
  have hgrad0 : ∇ f xStar = 0 := hf'.gradient_eq_zero_of_isMinOn hxStar
  have hgap :
      f x0 - f xStar ≤ (L[2](f) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    -- The Chapter 2 smooth upper tangent bound at the minimizer converts distance control
    -- into the objective-gap form used in the Newton region inequality.
    have hupper :
        f x0 ≤ f xStar + (L[2](f) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      simpa [hgrad0] using hf'.upper_tangent_quadratic xStar x0
    linarith
  rw [mem_newtonQuadraticConvergenceRegion_iff]
  have hscaled :
      (2 : ℝ) * L[3](f) ^ (2 : ℕ) * (f x0 - f xStar) ≤
        L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    -- Multiply the upper tangent gap bound by the nonnegative canonical Hessian-Lipschitz factor.
    have hL3_nonneg : 0 ≤ (L[3](f) : ℝ) := by positivity
    nlinarith [hgap, hL3_nonneg]
  exact le_trans hscaled hratio

/-- Helper for Text 4 2 24: the unit-scale hyperbolic denominator dominates the polynomial factor
`(4 + s^2) * s^2`. -/
private lemma four_add_sq_mul_sq_le_expSubExpNeg_sq
    {s : ℝ} (hs_nonneg : 0 ≤ s) :
    (4 + s ^ (2 : ℕ)) * s ^ (2 : ℕ) ≤
      (Real.exp s - Real.exp (-s)) ^ (2 : ℕ) := by
  let u : ℝ := Real.arsinh (s / 2)
  have hu_nonneg : 0 ≤ u := by
    -- The `arsinh` argument is nonnegative, so the barrier point `u` lies in `[0, ∞)`.
    have hs_half_nonneg : 0 ≤ s / 2 := by positivity
    have hmono : Monotone Real.arsinh := fun a b hab ↦ (Real.arsinh_le_arsinh).2 hab
    simpa [u] using hmono hs_half_nonneg
  have hu_le : 2 * u ≤ s := by
    -- Apply `x ≤ sinh x` at `u = arsinh (s / 2)` and rewrite the right-hand side back to `s / 2`.
    have hself_le : u ≤ Real.sinh u := (Real.self_le_sinh_iff).2 hu_nonneg
    have hscaled := mul_le_mul_of_nonneg_left hself_le (by positivity : 0 ≤ (2 : ℝ))
    have hu_half : u ≤ s / 2 := by
      simpa [u, Real.sinh_arsinh] using hscaled
    nlinarith
  have hsinh_lower :
      s * Real.sqrt (1 + (s / 2) ^ (2 : ℕ)) ≤ Real.sinh s := by
    -- Monotonicity of `sinh` turns the `arsinh` barrier into the exact polynomial lower bound.
    have hsinh_mono : Real.sinh (2 * u) ≤ Real.sinh s := (Real.sinh_le_sinh).2 hu_le
    dsimp [u] at hsinh_mono
    rw [Real.sinh_two_mul, Real.sinh_arsinh, Real.cosh_arsinh] at hsinh_mono
    nlinarith
  have hexp_lower :
      2 * s * Real.sqrt (1 + (s / 2) ^ (2 : ℕ)) ≤ Real.exp s - Real.exp (-s) := by
    -- Rewrite `sinh` back to the exponential denominator used in Chapter 2.
    have hsinh_exp : s * Real.sqrt (1 + (s / 2) ^ (2 : ℕ)) ≤ (Real.exp s - Real.exp (-s)) / 2 := by
      rw [Real.sinh_eq] at hsinh_lower
      exact hsinh_lower
    nlinarith [hsinh_exp]
  have hleft_nonneg : 0 ≤ 2 * s * Real.sqrt (1 + (s / 2) ^ (2 : ℕ)) := by
    positivity
  have hright_nonneg : 0 ≤ Real.exp s - Real.exp (-s) := le_trans hleft_nonneg hexp_lower
  have hsq :
      (2 * s * Real.sqrt (1 + (s / 2) ^ (2 : ℕ))) ^ (2 : ℕ) ≤
        (Real.exp s - Real.exp (-s)) ^ (2 : ℕ) := by
    exact (sq_le_sq₀ hleft_nonneg hright_nonneg).2 hexp_lower
  have hsqrt_arg_nonneg : 0 ≤ 1 + (s / 2) ^ (2 : ℕ) := by positivity
  have hleft_eq :
      (2 * s * Real.sqrt (1 + (s / 2) ^ (2 : ℕ))) ^ (2 : ℕ) =
        (4 + s ^ (2 : ℕ)) * s ^ (2 : ℕ) := by
    have hsqrt_sq :
          Real.sqrt (1 + (s / 2) ^ (2 : ℕ)) * Real.sqrt (1 + (s / 2) ^ (2 : ℕ)) =
            1 + (s / 2) ^ (2 : ℕ) := by
        rw [← sq, Real.sq_sqrt hsqrt_arg_nonneg]
    have hsqrt_sq' :
        (Real.sqrt (1 + (s / 2) ^ (2 : ℕ))) ^ (2 : ℕ) = 1 + (s / 2) ^ (2 : ℕ) := by
      rw [sq, hsqrt_sq]
    calc
        (2 * s * Real.sqrt (1 + (s / 2) ^ (2 : ℕ))) ^ (2 : ℕ)
            = 4 * s ^ (2 : ℕ) * (Real.sqrt (1 + (s / 2) ^ (2 : ℕ))) ^ (2 : ℕ) := by
                ring
        _ = 4 * s ^ (2 : ℕ) * (1 + (s / 2) ^ (2 : ℕ)) := by rw [hsqrt_sq']
        _ = (4 + s ^ (2 : ℕ)) * s ^ (2 : ℕ) := by ring
  calc
    (4 + s ^ (2 : ℕ)) * s ^ (2 : ℕ)
        = (2 * s * Real.sqrt (1 + (s / 2) ^ (2 : ℕ))) ^ (2 : ℕ) := hleft_eq.symm
    _ ≤ (Real.exp s - Real.exp (-s)) ^ (2 : ℕ) := hsq

/-- Helper for Text 4 2 24: substituting the canonical ratio `R` rewrites the Chapter 2
hyperbolic-gap coefficient into the Chapter 4 Newton-region numerator. -/
private lemma methodGapToNewtonRegionCoefficient
    {σ L M dist R : ℝ}
    (hσ_pos : 0 < σ) (hL_pos : 0 < L)
    (hR : R = (L * M ^ (2 : ℕ) * dist ^ (2 : ℕ)) / σ ^ (3 : ℕ)) :
    (4 * (4 + q[σ, L]) * σ * M ^ (2 : ℕ) * dist ^ (2 : ℕ)) / 3 =
      ((4 * (4 + q[σ, L]) * q[σ, L] * R) / 3) * σ ^ (3 : ℕ) := by
  -- Rewrite `q[σ,L] = σ / L` and substitute the ratio `R` once, so later proofs only compare
  -- scalar denominator bounds.
  rw [hR]
  field_simp [hσ_pos.ne', hL_pos.ne']

/-- Helper for Text 4 2 24: the ceiling candidate `Nat.ceil a + 1` stays within one additive step
of the real threshold `2 + a`. -/
private lemma entryCandidateCeilBounds
    {a : ℝ} (ha_nonneg : 0 ≤ a) :
    (((Nat.ceil a + 1 : ℕ) : ℝ) ≤ 2 + a) ∧
      (2 + a ≤ (((Nat.ceil a + 1 : ℕ) + 1 : ℕ) : ℝ)) := by
  constructor
  · -- The ceiling is at most one unit above `a`, so the candidate index is at most `2 + a`.
    have hceil_lt : ((Nat.ceil a : ℕ) : ℝ) < a + 1 := by
      exact_mod_cast Nat.ceil_lt_add_one ha_nonneg
    calc
      (((Nat.ceil a + 1 : ℕ) : ℝ)) = (Nat.ceil a : ℝ) + 1 := by norm_num
      _ ≤ (a + 1) + 1 := by linarith
      _ = 2 + a := by ring
  · -- The ceiling is always above `a`, so one more successor dominates `2 + a`.
    have ha_le : a ≤ ((Nat.ceil a : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_ceil a
    calc
      2 + a ≤ 2 + (Nat.ceil a : ℝ) := by gcongr
      _ = (Nat.ceil a : ℝ) + 2 := by ring
      _ = (((Nat.ceil a + 1 : ℕ) + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_add]
        norm_num
        ring

/-- Helper for Text 4 2 24: a lower bound on the Chapter 2 hyperbolic denominator places the
corresponding optimal-method iterate inside Newton's quadratic-convergence region. -/
private lemma method_memNewtonQuadraticConvergenceRegion_of_denominatorSqBound
    {f : E → ℝ} [f ∈ 𝓕₂Lip] {x0 xStar : E}
    (hxStar : IsMinOn f Set.univ xStar)
    (method :
      GeneralOptimalMethodScheme f L[2](f) σ[2](f) x0
        (3 * L[2](f) + σ[2](f)))
    {R : ℝ}
    (hR :
      R =
        (L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          σ[2](f) ^ (3 : ℕ))
    {k : ℕ}
    (hdenom :
      (4 * (4 + q[σ[2](f), L[2](f)]) * q[σ[2](f), L[2](f)] * R) / 3 ≤
        (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[σ[2](f), L[2](f)]) -
          Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[σ[2](f), L[2](f)]))) ^ (2 : ℕ)) :
    method k ∈ newtonQuadraticConvergenceRegion f xStar := by
  -- Route correction: rewrite the Chapter 2 numerator into the Chapter 4 coefficient first, so
  -- the remaining proof is a single denominator comparison.
  have hσ_pos : 0 < σ[2](f) :=
    IsInFunctionClassF2Lip.sigma_pos (inferInstance : f ∈ 𝓕₂Lip)
  have hL_pos : 0 < L[2](f) := method.L_pos
  set d : ℝ :=
    Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[σ[2](f), L[2](f)]) -
      Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[σ[2](f), L[2](f)])) with hd
  have hq_pos : 0 < q[σ[2](f), L[2](f)] := div_pos hσ_pos hL_pos
  have ht_pos : 0 < (((k + 1 : ℝ) / 2) * Real.sqrt q[σ[2](f), L[2](f)]) := by
    have hsqrt_pos : 0 < Real.sqrt q[σ[2](f), L[2](f)] := Real.sqrt_pos.2 hq_pos
    positivity
  have hd_pos : 0 < d := by
    -- The hyperbolic denominator is positive because its exponential arguments are ordered.
    refine sub_pos.mpr ?_
    exact Real.exp_lt_exp.mpr (by linarith)
  have hd_sq_pos : 0 < d ^ (2 : ℕ) := pow_pos hd_pos 2
  have hdenom' :
      (4 * (4 + q[σ[2](f), L[2](f)]) * q[σ[2](f), L[2](f)] * R) / 3 ≤ d ^ (2 : ℕ) := by
    simpa [d] using hdenom
  rw [mem_newtonQuadraticConvergenceRegion_iff]
  have hgap :=
    optimal_method_hyperbolic_suboptimality_le method f2Lip_memS11 hxStar k
  have hscaled :
      (2 : ℝ) * L[3](f) ^ (2 : ℕ) * (f (method k) - f xStar) ≤
        (2 : ℝ) * L[3](f) ^ (2 : ℕ) *
          ((2 * (4 + q[σ[2](f), L[2](f)]) * σ[2](f) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            (3 * d ^ (2 : ℕ))) := by
    -- Multiply the Chapter 2 objective-gap bound by the nonnegative Hessian-Lipschitz factor.
    have hL3_nonneg : 0 ≤ (2 : ℝ) * L[3](f) ^ (2 : ℕ) := by positivity
    simpa [d] using mul_le_mul_of_nonneg_left hgap hL3_nonneg
  calc
    (2 : ℝ) * L[3](f) ^ (2 : ℕ) * (f (method k) - f xStar)
        ≤
          (2 : ℝ) * L[3](f) ^ (2 : ℕ) *
            ((2 * (4 + q[σ[2](f), L[2](f)]) * σ[2](f) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
              (3 * d ^ (2 : ℕ))) := hscaled
    _ =
        ((4 * (4 + q[σ[2](f), L[2](f)]) * σ[2](f) * L[3](f) ^ (2 : ℕ) *
              ‖x0 - xStar‖ ^ (2 : ℕ)) / 3) /
          d ^ (2 : ℕ) := by
            field_simp [hd_pos.ne']
            ring
    _ =
        (((4 * (4 + q[σ[2](f), L[2](f)]) * q[σ[2](f), L[2](f)] * R) / 3) *
            σ[2](f) ^ (3 : ℕ)) /
          d ^ (2 : ℕ) := by
            have hcoef :=
              methodGapToNewtonRegionCoefficient
                (σ := σ[2](f)) (L := L[2](f)) (M := L[3](f))
                (dist := ‖x0 - xStar‖) hσ_pos hL_pos hR
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              congrArg (fun z : ℝ ↦ z / d ^ (2 : ℕ)) hcoef
    _ ≤ σ[2](f) ^ (3 : ℕ) := by
      -- The denominator bound is now exactly the scalar comparison needed to remove the fraction.
      refine (div_le_iff₀ hd_sq_pos).2 ?_
      have hσ3_nonneg : 0 ≤ σ[2](f) ^ (3 : ℕ) := by positivity
      calc
        ((4 * (4 + q[σ[2](f), L[2](f)]) * q[σ[2](f), L[2](f)] * R) / 3) *
            σ[2](f) ^ (3 : ℕ)
            ≤ d ^ (2 : ℕ) * σ[2](f) ^ (3 : ℕ) := by
              exact mul_le_mul_of_nonneg_right hdenom' hσ3_nonneg
        _ = σ[2](f) ^ (3 : ℕ) * d ^ (2 : ℕ) := by ring

/-- Helper for Text 4 2 24: when the canonical ratio is at most `4 / 3`, the third optimal-method
iterate already yields a large enough hyperbolic denominator. -/
private lemma hyperbolicDenominatorSq_ge_smallRatio
    {σ L R : ℝ}
    (hσ_pos : 0 < σ) (hL_pos : 0 < L) (hσ_le_L : σ ≤ L)
    (hR_nonneg : 0 ≤ R) (hR_le : R ≤ 4 / 3) :
    (4 * (4 + q[σ, L]) * q[σ, L] * R) / 3 ≤
      (Real.exp (((3 : ℝ) / 2) * Real.sqrt q[σ, L]) -
        Real.exp (-(((3 : ℝ) / 2) * Real.sqrt q[σ, L]))) ^ (2 : ℕ) := by
  set d : ℝ :=
    Real.exp (((3 : ℝ) / 2) * Real.sqrt q[σ, L]) -
      Real.exp (-(((3 : ℝ) / 2) * Real.sqrt q[σ, L])) with hd
  have hq_nonneg : 0 ≤ q[σ, L] := div_nonneg hσ_pos.le hL_pos.le
  have hq_le_one : q[σ, L] ≤ 1 := by
    -- The Chapter 2 reciprocal condition number is at most one when `σ ≤ L`.
    rw [show q[σ, L] = σ / L by rfl]
    exact (div_le_iff₀ hL_pos).2 (by simpa using hσ_le_L)
  have hq_pos : 0 < q[σ, L] := div_pos hσ_pos hL_pos
  have hd_pos : 0 < d := by
    -- At `k = 2`, the hyperbolic denominator is still strictly positive.
    refine sub_pos.mpr ?_
    exact Real.exp_lt_exp.mpr (by
      have hsqrt_pos : 0 < Real.sqrt q[σ, L] := Real.sqrt_pos.2 hq_pos
      linarith)
  have hquad_factor :
      9 * q[σ, L] ≤ d ^ (2 : ℕ) := by
    -- Rewrite the chapter comparison `σ / d² ≤ L / 9` as `9 * q[σ,L] ≤ d²`.
    have hbase0 := optimal_method_hyperbolic_factor_le_quadratic_factor hσ_pos hL_pos 2
    norm_num at hbase0
    have hbase : σ / d ^ (2 : ℕ) ≤ L / 9 := by
      simpa [d] using hbase0
    have htmp : σ ≤ (L / 9) * d ^ (2 : ℕ) := (div_le_iff₀ (pow_pos hd_pos 2)).1 hbase
    have htmp' : 9 * σ ≤ L * d ^ (2 : ℕ) := by
      nlinarith
    have hdiv : 9 * σ / L ≤ d ^ (2 : ℕ) := by
      exact (div_le_iff₀ hL_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using htmp')
    simpa [show q[σ, L] = σ / L by rfl, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hdiv
  have hcoeff :
      (4 * (4 + q[σ, L]) * q[σ, L] * R) / 3 ≤ 9 * q[σ, L] := by
    -- The middle regime keeps both `R` and `q[σ,L]` within the fixed polynomial window.
    have hpoly : (4 * (4 + q[σ, L]) * R) / 3 ≤ 9 := by
      nlinarith
    calc
      (4 * (4 + q[σ, L]) * q[σ, L] * R) / 3 = q[σ, L] * ((4 * (4 + q[σ, L]) * R) / 3) := by
        ring
      _ ≤ q[σ, L] * 9 := mul_le_mul_of_nonneg_left hpoly hq_nonneg
      _ = 9 * q[σ, L] := by ring
  exact le_trans hcoeff (by simpa [d] using hquad_factor)

/-- Helper for Text 4 2 24: once the canonical ratio is at least `4 / 3`, the logarithmic
threshold forces the Chapter 2 hyperbolic denominator to dominate the Chapter 4 entry factor. -/
private lemma hyperbolicDenominatorSq_ge_logThreshold_largeRatio
    {σ L R : ℝ}
    (hσ_pos : 0 < σ) (hL_pos : 0 < L)
    (hR_ge : 4 / 3 ≤ R)
    {k : ℕ}
    (hk :
      2 + 4 * (Real.sqrt (L / σ) * Real.log R) ≤ (k + 1 : ℝ)) :
    (4 * (4 + q[σ, L]) * q[σ, L] * R) / 3 ≤
      (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[σ, L]) -
        Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[σ, L]))) ^ (2 : ℕ) := by
  -- Route correction: keep the large branch purely scalar by comparing the chapter denominator
  -- against `R * (exp √q - exp (-√q))`, then use the existing barrier lemma.
  let qf : ℝ := q[σ, L]
  let s : ℝ := Real.sqrt qf
  let t : ℝ := ((k + 1 : ℝ) / 2) * s
  let d : ℝ := Real.exp t - Real.exp (-t)
  let ds : ℝ := Real.exp s - Real.exp (-s)
  have hR_pos : 0 < R := by nlinarith
  have hR_ge_one : 1 ≤ R := by nlinarith
  have hq_nonneg : 0 ≤ qf := by
    dsimp [qf]
    exact div_nonneg hσ_pos.le hL_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg qf
  have hs_mul : s * Real.sqrt (L / σ) = 1 := by
    -- The reciprocal condition number and its inverse square root cancel exactly.
    calc
      s * Real.sqrt (L / σ) = Real.sqrt (qf * (L / σ)) := by
        dsimp [s]
        rw [Real.sqrt_mul hq_nonneg]
      _ = Real.sqrt 1 := by
        congr 1
        dsimp [qf]
        field_simp [hσ_pos.ne', hL_pos.ne']
      _ = 1 := by rw [Real.sqrt_one]
  have hscaled :
      s + 2 * Real.log R ≤ t := by
    -- Multiply the threshold inequality by `√q[σ,L] / 2` and collapse the mixed square roots.
    have hmul :
        (s / 2) * (2 + 4 * (Real.sqrt (L / σ) * Real.log R)) ≤
          (s / 2) * (k + 1 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ s / 2)
    have hleft :
        (s / 2) * (2 + 4 * (Real.sqrt (L / σ) * Real.log R)) =
          s + 2 * Real.log R := by
      calc
        (s / 2) * (2 + 4 * (Real.sqrt (L / σ) * Real.log R)) =
            s + 2 * (s * Real.sqrt (L / σ)) * Real.log R := by ring
        _ = s + 2 * Real.log R := by
          rw [hs_mul]
          ring
    have hright : (s / 2) * (k + 1 : ℝ) = t := by
      dsimp [t]
      ring
    simpa [hleft, hright] using hmul
  have hscaled' : s + Real.log R ≤ t := by
    have hlog_nonneg : 0 ≤ Real.log R := Real.log_nonneg hR_ge_one
    linarith
  have hRexp : R * Real.exp s ≤ Real.exp t := by
    -- Exponentiating `s + log R ≤ t` gives the forward denominator comparison.
    calc
      R * Real.exp s = Real.exp s * R := by ring
      _ = Real.exp (s + Real.log R) := by
        rw [Real.exp_add, Real.exp_log hR_pos]
      _ ≤ Real.exp t := by
        exact Real.exp_le_exp.mpr hscaled'
  have hexp_div : Real.exp (-t) ≤ Real.exp (-s) / R := by
    -- The same inequality with negated exponents gives the reverse tail comparison.
    calc
      Real.exp (-t) ≤ Real.exp (-(s + Real.log R)) := by
        exact Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-s) * (1 / R) := by
        rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hR_pos]
        ring
      _ = Real.exp (-s) / R := by ring
  have hInv_le_R : 1 / R ≤ R := by
    exact (div_le_iff₀ hR_pos).2 (by nlinarith [hR_ge_one])
  have hneg_compare : Real.exp (-s) / R ≤ R * Real.exp (-s) := by
    have hexp_nonneg : 0 ≤ Real.exp (-s) := by positivity
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hInv_le_R hexp_nonneg
  have hRds_le : R * ds ≤ d := by
    -- First compare the exponential tails termwise, then revert to the hyperbolic denominators.
    have hterm :
        R * Real.exp s - Real.exp (-s) / R ≤ d := by
      dsimp [d]
      linarith
    dsimp [ds]
    linarith
  have hds_nonneg : 0 ≤ ds := by
    dsimp [ds]
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hRds_nonneg : 0 ≤ R * ds := by positivity
  have hd_nonneg : 0 ≤ d := le_trans hRds_nonneg hRds_le
  have hbarrier :
      (4 + qf) * qf ≤ ds ^ (2 : ℕ) := by
    -- Convert the proved barrier from `s` back to `q[σ,L] = s²`.
    have hbase := four_add_sq_mul_sq_le_expSubExpNeg_sq hs_nonneg
    have hs_sq : s ^ (2 : ℕ) = qf := by
      dsimp [s]
      rw [Real.sq_sqrt hq_nonneg]
    calc
      (4 + qf) * qf = (4 + s ^ (2 : ℕ)) * s ^ (2 : ℕ) := by rw [hs_sq]
      _ ≤ ds ^ (2 : ℕ) := by simpa [ds] using hbase
  have hcoeff_le :
      (4 * (4 + qf) * qf * R) / 3 ≤ ((4 * R) / 3) * ds ^ (2 : ℕ) := by
    have hscale_nonneg : 0 ≤ (4 * R) / 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbarrier hscale_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hRscale :
      ((4 * R) / 3) * ds ^ (2 : ℕ) ≤ R ^ (2 : ℕ) * ds ^ (2 : ℕ) := by
    have hfactor : (4 * R) / 3 ≤ R ^ (2 : ℕ) := by
      nlinarith
    exact mul_le_mul_of_nonneg_right hfactor (sq_nonneg ds)
  have hsq_compare : R ^ (2 : ℕ) * ds ^ (2 : ℕ) ≤ d ^ (2 : ℕ) := by
    calc
      R ^ (2 : ℕ) * ds ^ (2 : ℕ) = (R * ds) ^ (2 : ℕ) := by ring
      _ ≤ d ^ (2 : ℕ) := (sq_le_sq₀ hRds_nonneg hd_nonneg).2 hRds_le
  exact
    le_trans hcoeff_le <|
      le_trans hRscale <|
        by simpa [qf, d] using hsq_compare

/-- Text 4 2 24: for the class `σ₂(f) > 0`, `L₂(f) < ∞`, `L₃(f) < ∞`, standard optimal
first-order methods can enter Newton's quadratic-convergence region `Q_f` within
`O(√(L₂(f) / σ₂(f)) * log ((L₂(f) * L₃(f)^2 / σ₂(f)^3) * ‖x₀ - xStar‖^2))` iterations. The
explicit nonnegative owner `newtonQuadraticConvergenceEntryBound f x₀ xStar C` records this
logarithmic threshold with a two-step natural-index safety offset. -/
theorem newton_enters_quadratic_convergence_region_of_f2Lip
    : ∃ C > 0,
        ∀ {f : E → ℝ} [f ∈ 𝓕₂Lip] {x0 : E}
          (xStar : E)
          (_ : IsMinOn f Set.univ xStar)
          (method :
            GeneralOptimalMethodScheme f L[2](f) σ[2](f) x0
              (3 * L[2](f) + σ[2](f))),
            ∃ k : ℕ,
              (k : ℝ) ≤ newtonQuadraticConvergenceEntryBound f x0 xStar C ∧
                method k ∈ newtonQuadraticConvergenceRegion f xStar := by
  refine ⟨4, by positivity, ?_⟩
  intro f _ x0 xStar hxStar method
  -- Route correction: split only by the canonical ratio `R`, and route both nontrivial cases
  -- through the denominator bridge proved above.
  let R : ℝ :=
    (L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
      σ[2](f) ^ (3 : ℕ)
  have hR :
      R =
        (L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          σ[2](f) ^ (3 : ℕ) := by
    rfl
  have hσ_pos : 0 < σ[2](f) :=
    IsInFunctionClassF2Lip.sigma_pos (inferInstance : f ∈ 𝓕₂Lip)
  have hL_pos : 0 < L[2](f) := method.L_pos
  by_cases hE : Subsingleton E
  · refine ⟨0, ?_, ?_⟩
    · -- The entry bound always has an additive offset `2`, so `k = 0` is admissible.
      have htail_nonneg :
          0 ≤
            max 0
              (4 *
                (Real.sqrt (L[2](f) / σ[2](f)) *
                  Real.log
                    ((L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
                      σ[2](f) ^ (3 : ℕ)))) := by
        exact le_max_left _ _
      dsimp [newtonQuadraticConvergenceEntryBound]
      linarith
    · -- On a subsingleton space the initial point is already the minimizer, so the region test is
      -- immediate at `k = 0`.
      have hx0 : x0 = xStar := hE.elim x0 xStar
      have hmethod0 : method 0 = xStar := by
        simpa [hx0] using method.x_zero
      rw [hmethod0, mem_newtonQuadraticConvergenceRegion_iff]
      have hσ3_nonneg : 0 ≤ σ[2](f) ^ (3 : ℕ) := by positivity
      simpa using hσ3_nonneg
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hσ_le_L : σ[2](f) ≤ L[2](f) := (mem_S11_iff.mp f2Lip_memS11).mu_le_L
    by_cases hR_le_one : R ≤ 1
    · refine ⟨0, ?_, ?_⟩
      · -- The entry bound always has an additive offset `2`, so `k = 0` is admissible.
        have htail_nonneg :
            0 ≤
              max 0
                (4 *
                  (Real.sqrt (L[2](f) / σ[2](f)) *
                    Real.log
                      ((L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
                        σ[2](f) ^ (3 : ℕ)))) := by
          exact le_max_left _ _
        dsimp [newtonQuadraticConvergenceEntryBound]
        linarith
      · -- In the small-ratio regime, the initial point already satisfies the Newton-region test.
        have hratio_scaled :
            R * σ[2](f) ^ (3 : ℕ) =
              L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
          rw [hR]
          field_simp [hσ_pos.ne']
        have hratio :
            L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤ σ[2](f) ^ (3 : ℕ) := by
          calc
            L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ) =
                R * σ[2](f) ^ (3 : ℕ) := hratio_scaled.symm
            _ ≤ σ[2](f) ^ (3 : ℕ) := by
              have hσ3_nonneg : 0 ≤ σ[2](f) ^ (3 : ℕ) := by positivity
              nlinarith
        simpa [method.x_zero] using
          mem_newtonQuadraticConvergenceRegion_of_ratio_le_one hxStar hratio
    · have hR_gt_one : 1 < R := lt_of_not_ge hR_le_one
      have hR_pos : 0 < R := by linarith
      by_cases hR_le_fourThird : R ≤ 4 / 3
      · refine ⟨2, ?_, ?_⟩
        · -- The middle branch uses the fixed iterate `k = 2`, which always lies below the bound.
          have htail_nonneg :
              0 ≤
                max 0
                  (4 *
                    (Real.sqrt (L[2](f) / σ[2](f)) *
                      Real.log
                        ((L[2](f) * L[3](f) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
                          σ[2](f) ^ (3 : ℕ)))) := by
            exact le_max_left _ _
          dsimp [newtonQuadraticConvergenceEntryBound]
          linarith
        · -- The fixed denominator bound at `k = 2` now feeds directly into the transport lemma.
          have hR_nonneg : 0 ≤ R := by linarith
          have hdenom :=
            hyperbolicDenominatorSq_ge_smallRatio
              hσ_pos hL_pos hσ_le_L hR_nonneg hR_le_fourThird
          exact
            method_memNewtonQuadraticConvergenceRegion_of_denominatorSqBound
              hxStar method hR (k := 2) (by
                norm_num
                simpa using hdenom)
      · have hR_ge : 4 / 3 ≤ R := by
          linarith
        let a : ℝ := 4 * (Real.sqrt (L[2](f) / σ[2](f)) * Real.log R)
        let k : ℕ := Nat.ceil a + 1
        refine ⟨k, ?_, ?_⟩
        · -- The generic ceiling bridge converts the logarithmic threshold into a natural index.
          have hR_ge_one : 1 ≤ R := by nlinarith [hR_ge]
          have hlog_nonneg : 0 ≤ Real.log R := Real.log_nonneg hR_ge_one
          have ha_nonneg : 0 ≤ a := by
            dsimp [a]
            positivity
          have hk_bound := (entryCandidateCeilBounds ha_nonneg).1
          have hbound_eq :
              newtonQuadraticConvergenceEntryBound f x0 xStar 4 = 2 + a := by
            dsimp [newtonQuadraticConvergenceEntryBound, a, R]
            rw [max_eq_right ha_nonneg]
          simpa [k, hbound_eq] using hk_bound
        · -- The large branch uses the ceiling threshold to instantiate the scalar denominator
          -- bound.
          have hR_ge_one : 1 ≤ R := by nlinarith [hR_ge]
          have hlog_nonneg : 0 ≤ Real.log R := Real.log_nonneg hR_ge_one
          have ha_nonneg : 0 ≤ a := by
            dsimp [a]
            positivity
          have hk_threshold :
              2 + 4 * (Real.sqrt (L[2](f) / σ[2](f)) * Real.log R) ≤ (k + 1 : ℝ) := by
            simpa [a, k] using (entryCandidateCeilBounds ha_nonneg).2
          have hdenom :=
            hyperbolicDenominatorSq_ge_logThreshold_largeRatio
              hσ_pos hL_pos hR_ge hk_threshold
          exact
            method_memNewtonQuadraticConvergenceRegion_of_denominatorSqBound
              hxStar method hR (k := k) hdenom

end NewtonQuadraticConvergenceEntry
