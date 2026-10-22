/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.14 lies in the Chapter 5 posynomial / positive-orthant barrier-compatibility
domain.

Sampled owner declarations:
* `ambientMonomialXi` and `ξ_[a]` from `Definition_5_4_7_17`, the ambient/source-facing owners for
  simplex monomials;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for barrier compatibility;
* `IsBetaCompatibleWith.smul` and `IsBetaCompatibleWith.add` from `Theorem_5_4_6_2`, the canonical
  closure API for positive combinations;
* `monomial_isOneCompatibleWith_positiveOrthantLogarithmicBarrier` from `Theorem_5_4_7_13`, the
  monomial compatibility owner theorem.

Best owner abstraction:
* source-facing: `posynomialXi` on the strict positive orthant;
* core/canonical: `IsBetaCompatibleWith` applied to the ambient finite sum of monomial terms;
* bridge/view: evaluation of that ambient finite sum on `positiveOrthant n`.

Primitive data:
* the positive coefficients `α : Fin m → Set.Ioi (0 : ℝ)`;
* the simplex exponents `a : Fin m → Δ[n]`.

Derived API:
* the source-facing owner `posynomialXi`;
* its evaluation lemma `posynomialXi_apply`;
* the bridge lemma identifying the corresponding ambient finite sum with `posynomialXi` on
  `positiveOrthant n`;
* the compatibility theorem for that ambient finite sum.

The previous version introduced a second public owner `ambientPosynomialXi` whose only role was to
repackage the ambient finite combination already determined by the monomial owners and the
`IsBetaCompatibleWith` closure API. This refinement keeps `posynomialXi` as the public owner,
adds a named bridge from the canonical ambient finite sum to `posynomialXi`, and uses that bridge
to keep the source-facing posynomial connected to the ambient compatibility surface without
preserving a parallel wrapper.
-/

/-- The posynomial `ξ(x) = \sum_{k=1}^m α_k x^{a_k}` on the strict positive orthant. -/
def posynomialXi
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n]) :
    positiveOrthant n → ℝ :=
  ∑ k : Fin m, (α k : ℝ) • ξ_[(a k)]

/-- Evaluating `posynomialXi n m α a` at a positive vector gives the textbook sum formula. -/
@[simp] theorem posynomialXi_apply
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n])
    (x : positiveOrthant n) :
    posynomialXi n m α a x =
      ∑ k : Fin m, (α k : ℝ) * ξ_[(a k)] x := by
  simp [posynomialXi, smul_eq_mul]

/-- Restricting the canonical ambient finite sum of monomial terms to the strict positive orthant
recovers the source-facing posynomial `posynomialXi n m α a`. -/
@[simp] theorem sum_smul_ambientMonomialXi_eq_posynomialXi
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n])
    (x : positiveOrthant n) :
    (∑ k : Fin m, (α k : ℝ) • ambientMonomialXi (a k)) x = posynomialXi n m α a x := by
  simp [posynomialXi, smul_eq_mul]

namespace IsBetaCompatibleWith

/-- Helper for Theorem 5.4.7.14: every `β`-compatible map has zero compatibility expression in
the cone, so `(0 : E₂) ∈ K`. -/
private lemma zero_mem
    {E₁ : Type*} {E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {β : NNReal} {ξ : E₁ → E₂}
    (hξ : IsBetaCompatibleWith Q₁ K F β ξ) :
    (0 : E₂) ∈ K := by
  -- Evaluate the compatibility inequality at the zero direction so both derivatives vanish.
  rcases hξ.interior_nonempty with ⟨x, hx⟩
  have hD2 : vectorSecondDirectionalDerivative ξ x (0 : E₁) = 0 := by
    simpa [vectorSecondDirectionalDerivative] using
      (iteratedFDeriv ℝ 2 ξ x).map_coord_zero (0 : Fin 2) rfl
  have hD3 : vectorThirdDirectionalDerivative ξ x (0 : E₁) = 0 := by
    simpa [vectorThirdDirectionalDerivative] using
      (iteratedFDeriv ℝ 3 ξ x).map_coord_zero (0 : Fin 3) rfl
  simpa [hD2, hD3] using hξ.compatibility_bound hx (0 : E₁)

/-- Helper for Theorem 5.4.7.14: nonnegative scalar multiples preserve
`IsBetaCompatibleWith Q₁ K F β`. -/
private theorem smul
    {E₁ : Type*} {E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {β : NNReal} {ξ : E₁ → E₂}
    (hξ : IsBetaCompatibleWith Q₁ K F β ξ)
    (α : NNReal) :
    IsBetaCompatibleWith Q₁ K F β (α • ξ) := by
  refine
    { convex_domain := hξ.convex_domain
      interior_nonempty := hξ.interior_nonempty
      one_le_parameter := hξ.one_le_parameter
      selfConcordantBarrier := hξ.selfConcordantBarrier
      contDiffOn := ?_
      compatibility_bound := ?_ }
  · -- Constant scaling preserves the `C³` regularity of the map.
    simpa using hξ.contDiffOn.const_smul (α : ℝ)
  · -- The compatibility expression scales by the same nonnegative factor.
    intro x hx h
    have hξx : ContDiffAt ℝ 3 ξ x :=
      hξ.contDiffOn.contDiffAt (isOpen_interior.mem_nhds hx)
    have hξx₂ : ContDiffAt ℝ 2 ξ x := hξx.of_le (by norm_num)
    have hscaled :
        (3 * (β : ℝ) * hessianLocalNorm F x h) •
            (-vectorSecondDirectionalDerivative (α • ξ) x h) -
          vectorThirdDirectionalDerivative (α • ξ) x h =
          (α : ℝ) •
            ((3 * (β : ℝ) * hessianLocalNorm F x h) •
                (-vectorSecondDirectionalDerivative ξ x h) -
              vectorThirdDirectionalDerivative ξ x h) := by
      rw [vectorSecondDirectionalDerivative, vectorThirdDirectionalDerivative,
        iteratedFDeriv_const_smul_apply hξx₂, iteratedFDeriv_const_smul_apply hξx]
      simp [NNReal.smul_def, sub_eq_add_neg, smul_add, smul_neg, smul_smul, mul_comm]
    rcases lt_or_eq_of_le α.2 with hα | hα
    · rw [hscaled]
      exact K.smul_mem hα (hξ.compatibility_bound hx h)
    · rw [hscaled]
      have hα' : (α : ℝ) = 0 := hα.symm
      simpa [hα'] using (hξ.zero_mem : (0 : E₂) ∈ K)

/-- Helper for Theorem 5.4.7.14: sums preserve `IsBetaCompatibleWith Q₁ K F β`. -/
private theorem add
    {E₁ : Type*} {E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {β : NNReal}
    {ξ₁ ξ₂ : E₁ → E₂}
    (hξ₁ : IsBetaCompatibleWith Q₁ K F β ξ₁)
    (hξ₂ : IsBetaCompatibleWith Q₁ K F β ξ₂) :
    IsBetaCompatibleWith Q₁ K F β (ξ₁ + ξ₂) := by
  refine
    { convex_domain := hξ₁.convex_domain
      interior_nonempty := hξ₁.interior_nonempty
      one_le_parameter := hξ₁.one_le_parameter
      selfConcordantBarrier := hξ₁.selfConcordantBarrier
      contDiffOn := ?_
      compatibility_bound := ?_ }
  · -- Regularity is closed under addition.
    simpa using hξ₁.contDiffOn.add hξ₂.contDiffOn
  · -- The cone bound for the sum is the sum of the two cone bounds.
    intro x hx h
    have hξ₁x : ContDiffAt ℝ 3 ξ₁ x :=
      hξ₁.contDiffOn.contDiffAt (isOpen_interior.mem_nhds hx)
    have hξ₂x : ContDiffAt ℝ 3 ξ₂ x :=
      hξ₂.contDiffOn.contDiffAt (isOpen_interior.mem_nhds hx)
    have hξ₁x₂ : ContDiffAt ℝ 2 ξ₁ x := hξ₁x.of_le (by norm_num)
    have hξ₂x₂ : ContDiffAt ℝ 2 ξ₂ x := hξ₂x.of_le (by norm_num)
    rw [vectorSecondDirectionalDerivative, vectorThirdDirectionalDerivative,
      iteratedFDeriv_add_apply hξ₁x₂ hξ₂x₂, iteratedFDeriv_add_apply hξ₁x hξ₂x]
    simpa [vectorSecondDirectionalDerivative, vectorThirdDirectionalDerivative,
      sub_eq_add_neg, smul_add, add_comm, add_left_comm, add_assoc] using
      K.add_mem (hξ₁.compatibility_bound hx h) (hξ₂.compatibility_bound hx h)

end IsBetaCompatibleWith

/-- Helper for Theorem 5.4.7.14: the coordinate-`0` basis vector belongs to `Δ[(n + 1)]`. -/
private theorem standardSimplexFirstVertex_mem (n : ℕ) :
    (fun i : Fin (n + 1) ↦ if i = 0 then (1 : ℝ) else 0) ∈ Δ[(n + 1)] := by
  constructor
  · intro i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]
  · simp

/-- Helper for Theorem 5.4.7.14: the standard basis vertex of `Δ[(n + 1)]` at coordinate `0`. -/
private def standardSimplexFirstVertex (n : ℕ) : Δ[(n + 1)] :=
  ⟨fun i : Fin (n + 1) ↦ if i = 0 then (1 : ℝ) else 0, standardSimplexFirstVertex_mem n⟩

private theorem zero_isOneCompatibleWith_positiveOrthantLogarithmicBarrier :
    IsBetaCompatibleWith
      (positiveOrthant n)
      (ConvexCone.positive ℝ ℝ)
      (standardLogarithmicBarrierAmbient n)
      (1 : NNReal)
      (0 : Eₙ → ℝ) := by
  -- Route correction: the broken import used to provide closure under nonnegative scaling.
  -- We now prove the zero map directly in dimension `0` and otherwise obtain it by scaling a
  -- compatible monomial by the scalar `0`.
  cases n with
  | zero =>
      have horthant0 :
          (positiveOrthant 0 : Set (EuclideanSpace ℝ (Fin 0))) = Set.univ := by
        ext x
        simp [EuclideanSpace.mem_positiveOrthant_iff]
      have hbarrier0 :
          standardLogarithmicBarrierAmbient 0 =
            (fun _ : EuclideanSpace ℝ (Fin 0) ↦ (0 : ℝ)) := by
        funext x
        simp [standardLogarithmicBarrierAmbient]
      have hinteriorConvex :
          Convex ℝ (interior (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))) := by
        simpa using (convex_univ : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin 0))))
      refine
        { convex_domain := ?_
          interior_nonempty := ?_
          one_le_parameter := by norm_num
          selfConcordantBarrier := ?_
          contDiffOn := ?_
          compatibility_bound := ?_ }
      · -- In dimension `0`, the positive orthant is all of the ambient space.
        rw [horthant0]
        exact convex_univ
      · -- The same zero-dimensional orthant has a canonical interior point.
        refine ⟨0, ?_⟩
        simp [horthant0]
      · -- The zero barrier on the zero-dimensional space is trivially self-concordant.
        refine ⟨0, ?_⟩
        refine
          { toIsStandardSelfConcordantOn := ?_
            barrier_parameter_bound := ?_ }
        · refine
            { isOpen_domain := ?_
              contDiffOn := ?_
              convexOn := ?_
              third_deriv_bound := ?_ }
          · simp [horthant0]
          · rw [horthant0]
            rw [hbarrier0]
            simpa using
              (contDiffOn_const : ContDiffOn ℝ 3
                (fun _ : EuclideanSpace ℝ (Fin 0) ↦ (0 : ℝ))
                (interior (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))))
          · rw [horthant0]
            rw [hbarrier0]
            simpa using (convexOn_const (c := (0 : ℝ)) hinteriorConvex)
          · intro x hx h
            have hzero : h = 0 := Subsingleton.elim _ _
            subst h
            rw [hbarrier0]
            have hslice :
                directionalSlice (fun _ : EuclideanSpace ℝ (Fin 0) ↦ (0 : ℝ)) x 0 =
                  (fun _ : ℝ ↦ (0 : ℝ)) := by
              funext t
              simp [directionalSlice]
            rw [thirdDirectionalDerivative, hslice]
            simp [hessianLocalNorm]
        · intro x hx h
          have hzero : h = 0 := Subsingleton.elim _ _
          subst h
          rw [hbarrier0]
          simp
      · -- The zero map is `C³` on the whole zero-dimensional ambient space.
        rw [horthant0]
        simpa using
          (contDiffOn_const : ContDiffOn ℝ 3
            (fun _ : EuclideanSpace ℝ (Fin 0) ↦ (0 : ℝ))
            (interior (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))))
      · -- The zero map has vanishing second and third derivatives, so the cone bound is `0 ∈ K`.
        intro x hx h
        have hzero : h = 0 := Subsingleton.elim _ _
        subst h
        simp [vectorSecondDirectionalDerivative, vectorThirdDirectionalDerivative]
  | succ n =>
      -- In positive dimension, scale a compatible monomial witness by the scalar `0`.
      simpa using
        IsBetaCompatibleWith.smul
          (monomial_isOneCompatibleWith_positiveOrthantLogarithmicBarrier
            (n := n + 1) (standardSimplexFirstVertex n))
          (0 : NNReal)

/-- Theorem 5.4.7.14: the posynomial
`ξ(x) = \sum_{k=1}^m α_k x^{a_k}` with positive coefficients and simplex exponents is
`1`-compatible with the logarithmic barrier
`F(x) = -\sum_{i=1}^n \log x^{(i)}` on the positive orthant `\mathbb{R}^n_{++}`. -/
theorem posynomialXi_isOneCompatibleWith_positiveOrthantLogarithmicBarrier
    (m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n]) :
    IsBetaCompatibleWith
      (positiveOrthant n)
      (ConvexCone.positive ℝ ℝ)
      (standardLogarithmicBarrierAmbient n)
      (1 : NNReal)
      (∑ k : Fin m, (α k : ℝ) • ambientMonomialXi (a k)) := by
  -- The ambient function in the compatibility statement restricts to `posynomialXi n m α a`
  -- by `sum_smul_ambientMonomialXi_eq_posynomialXi`.
  induction m with
  | zero =>
      simpa using zero_isOneCompatibleWith_positiveOrthantLogarithmicBarrier
  | succ m ih =>
      have hhead :
          IsBetaCompatibleWith
            (positiveOrthant n)
            (ConvexCone.positive ℝ ℝ)
            (standardLogarithmicBarrierAmbient n)
            (1 : NNReal)
            ((α 0 : ℝ) • ambientMonomialXi (a 0)) := by
        simpa using
          IsBetaCompatibleWith.smul
            (monomial_isOneCompatibleWith_positiveOrthantLogarithmicBarrier (a 0))
            ⟨α 0, (α 0).2.le⟩
      have htail :
          IsBetaCompatibleWith
            (positiveOrthant n)
            (ConvexCone.positive ℝ ℝ)
            (standardLogarithmicBarrierAmbient n)
            (1 : NNReal)
            (∑ k : Fin m, ((α k.succ : Set.Ioi (0 : ℝ)) : ℝ) • ambientMonomialXi (a k.succ)) :=
        ih (fun k ↦ α k.succ) (fun k ↦ a k.succ)
      simpa [Fin.sum_univ_succ] using IsBetaCompatibleWith.add hhead htail

end
