/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_18
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.17 is a `bridge/view` item in the chapter convex-analysis API. Its owner abstraction
is still the chapter strong-dual finite-sum rule from `Theorem_3_18`; this file keeps only the
real-valued everywhere-finite specialization `subdifferentialAt`, rather than a parallel local
sum-rule API. -/
recall subdifferentialAt
recall is_convex_function_iff_convexOn_toReal
recall strongDualSubdifferential_finset_sum_eq_sum_of_nonempty_iInter_relativeInterior

-- Proof sketch: specialize the strong-dual finite-sum rule from Theorem 3.18 to the
-- extended-real coercions `y ↦ (f i y : EReal)`. Real-valued convexity gives the no-`⊥`
-- hypothesis and convexity of each coercion, while the effective domain of every summand is all
-- of `E`, so the relative-interior qualification is automatic.
/-- Theorem 3.17: for a finite family of real-valued convex functions on `E`, the subdifferential
at `x` of the pointwise sum is the pointwise sum of the individual subdifferentials at `x`. -/
theorem subdifferentialAt_finset_sum_eq_sum_subdifferentialAt
    {m : ℕ} (f : Fin m → E → ℝ) (x : E)
    (hconvex : ∀ i : Fin m, ConvexOn ℝ Set.univ (f i)) :
    subdifferentialAt (fun y ↦ ∑ i : Fin m, f i y) x =
      ∑ i : Fin m, subdifferentialAt (f i) x := by
  let F : Fin m → E → EReal := fun i y ↦ (f i y : EReal)
  have h_ne_bot : ∀ i : Fin m, ∀ y : E, F i y ≠ ⊥ := by
    intro i y
    simp [F]
  have hconvexF : ∀ i : Fin m, is_convex_function (F i) := by
    intro i
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro y hy
      simp [F]
    · simpa [F, effective_domain] using hconvex i
  have hqual : (⋂ i : Fin m, intrinsicInterior ℝ (effective_domain (F i))).Nonempty := by
    refine ⟨x, ?_⟩
    simp [F, effective_domain]
  have hsum :
      (fun y ↦ ((∑ i : Fin m, f i y : ℝ) : EReal)) = fun y ↦ ∑ i : Fin m, F i y := by
    funext y
    change Real.toEReal (∑ i : Fin m, f i y) =
      ∑ i : Fin m, Real.toEReal (f i y)
    exact
      map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
        (fun i : Fin m ↦ f i y) Finset.univ
  unfold subdifferentialAt
  rw [hsum]
  simpa [F] using
    strongDualSubdifferential_finset_sum_eq_sum_of_nonempty_iInter_relativeInterior
      F x h_ne_bot hconvexF hqual

end
