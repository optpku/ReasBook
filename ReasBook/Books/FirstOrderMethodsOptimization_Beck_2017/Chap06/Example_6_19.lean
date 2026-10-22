/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.proposition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Function

variable {E : Type u} [NormedAddCommGroup E]

attribute [local instance] Classical.propDecidable

/- Example 6.19 is `source-facing`: the public content is the radial proximal formula for the
norm penalty `x ↦ λ ‖x‖`, stated on the chapter owner `prox[...]`. Domain sampling against
Definition 6.1, Lemma 6.5 (1), Theorem 6.18, and Example 6.20 shows the owner split here:

- `source-facing`: the norm penalty `norm_penalty`,
- `core/canonical`: the chapter radial proximal owner `prox_norm_composition_eq_piecewise`,
- `bridge/view`: the scalar positive-ray owner `nonnegative_linear_penalty`.

The primitive data are only `lam` and the norm-based penalty itself; the scalar radial profile is
derived bridge data and should not remain as a parallel public owner in this file. -/

/-- The norm penalty `x ↦ λ ‖x‖`. -/
def norm_penalty (lam : ℝ) : E → EReal :=
  fun x ↦ ((lam * ‖x‖ : ℝ) : EReal)

/-- Evaluating `norm_penalty λ` at `x` gives the value `λ ‖x‖`. -/
@[simp] theorem norm_penalty_apply (lam : ℝ) (x : E) :
    norm_penalty lam x = ((lam * ‖x‖ : ℝ) : EReal) :=
  rfl

/-- The norm penalty is the radial lift of the scalar nonnegative-ray linear penalty. -/
theorem norm_penalty_eq_nonnegative_linear_penalty_comp_norm (lam : ℝ) :
    norm_penalty lam = nonnegative_linear_penalty lam ∘ (norm : E → ℝ) := by
  funext x
  simp [norm_penalty, nonnegative_linear_penalty, extendedIndicator]

section

variable [InnerProductSpace ℝ E]

private theorem lowerSemicontinuous_nonnegative_linear_penalty (lam : ℝ) :
    LowerSemicontinuous (nonnegative_linear_penalty lam) := by
  rw [lowerSemicontinuous_iff_isClosed_real_epigraph]
  have hepigraph :
      realEpigraph (nonnegative_linear_penalty lam) =
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ lam * p.1 ≤ p.2} := by
    ext p
    change nonnegative_linear_penalty lam p.1 ≤ (p.2 : EReal) ↔ 0 ≤ p.1 ∧ lam * p.1 ≤ p.2
    by_cases hp : 0 ≤ p.1
    · rw [nonnegative_linear_penalty_apply, if_pos hp]
      rw [EReal.coe_mul]
      constructor
      · intro h
        exact ⟨hp, EReal.coe_le_coe_iff.mp h⟩
      · intro h
        exact EReal.coe_le_coe_iff.mpr h.2
    · simp [nonnegative_linear_penalty_apply, hp]
  rw [hepigraph]
  have hnonneg : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hlinear : IsClosed {p : ℝ × ℝ | lam * p.1 ≤ p.2} :=
    isClosed_le (continuous_const.mul continuous_fst) continuous_snd
  simpa [Set.setOf_and] using hnonneg.inter hlinear

private theorem isConvexFunction_extendedIndicator_Ici :
    is_convex_function (extendedIndicator (Set.Ici (0 : ℝ))) := by
  have hconv : Convex ℝ (realEpigraph (δ_ (Set.Ici (0 : ℝ)))) := by
    rw [extendedIndicator_real_epigraph_eq]
    simpa using (convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ))
  simpa [is_convex_function, realEpigraph] using hconv

private theorem isConvex_nonnegative_linear_penalty (lam : ℝ) :
    is_convex_function (nonnegative_linear_penalty lam) := by
  have hind : is_convex_function (extendedIndicator (Set.Ici (0 : ℝ))) :=
    isConvexFunction_extendedIndicator_Ici
  have hlin : is_convex_function ((fun t : ℝ ↦ lam * t).toEReal) := by
    exact toEReal_isConvexFunction <| by
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b ha hb hab
      change lam * (a * x + b * y) ≤ a * (lam * x) + b * (lam * y)
      nlinarith [hab]
  simpa [nonnegative_linear_penalty, Function.toEReal, Pi.add_apply] using
    is_convex_function_pointwise_add hind hlin
      (by
        intro t
        by_cases ht : 0 ≤ t
        · simp [extendedIndicator, ht]
        · have ht' : t ∈ Set.Iio (0 : ℝ) := by
            simpa using ht
          simp [extendedIndicator, ht'])
      (by
        intro t
        exact EReal.coe_ne_bot _)

-- Proof sketch: identify the scalar radial profile of `norm_penalty lam` with the existing owner
-- `nonnegative_linear_penalty lam`, apply the chapter radial proximal theorem to that scalar
-- owner, and substitute the one-dimensional formula
-- `prox[nonnegative_linear_penalty lam] t = {(t - lam)⁺}` from Lemma 6.5. At the origin this
-- gives `{0}` in the trivial space and, in the nontrivial branch, the inner-product-space radial
-- theorem gives the shrinkage `((‖x‖ - lam)⁺ / ‖x‖) • x`; rewriting those regimes yields the
-- compact factor `1 - lam / max ‖x‖ lam` under the source assumption `0 < lam`.
/-- Example 6.19: in a real inner product space, for the norm penalty `f(x) = λ ‖x‖` with
`0 < λ`, the proximal
mapping at `x` is the singleton obtained by radial shrinkage:
`prox[f] x = {(1 - λ / max {‖x‖, λ}) • x}`. -/
theorem prox_norm_penalty_eq_singleton_shrinkage
    (lam : ℝ) (hlam : 0 < lam) (x : E) :
    prox[norm_penalty lam] x = {(1 - lam / max ‖x‖ lam) • x} := by
  by_cases hE : Subsingleton E
  · letI : Subsingleton E := hE
    have hx0 : x = 0 := Subsingleton.elim x 0
    have hprox0 : prox[norm_penalty lam] (0 : E) = {(0 : E)} := by
      refine Set.eq_singleton_iff_unique_mem.2 ?_
      constructor
      · rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
        intro y
        have hy : y = 0 := Subsingleton.elim y 0
        simp [hy]
      · intro y hy
        simpa using (Subsingleton.elim y 0)
    simpa [hx0, max_eq_right (le_of_lt hlam)] using hprox0
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hpiece :=
      prox_norm_composition_eq_piecewise
        (nonnegative_linear_penalty lam)
        (isProper_nonnegative_linear_penalty lam)
        (lowerSemicontinuous_nonnegative_linear_penalty lam)
        (isConvex_nonnegative_linear_penalty lam)
        (fun t ht ↦ by simp [nonnegative_linear_penalty_apply, not_le_of_gt ht])
        x
    have hprox :
        prox[norm_penalty lam] x =
          if x = 0 then
            {u : E | ‖u‖ ∈ prox[nonnegative_linear_penalty lam] 0}
          else
            (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_linear_penalty lam] ‖x‖ := by
      calc
        prox[norm_penalty lam] x =
            prox[nonnegative_linear_penalty lam ∘ (norm : E → ℝ)] x := by
          exact congrArg (fun f : E → EReal ↦ prox[f] x)
            (norm_penalty_eq_nonnegative_linear_penalty_comp_norm lam)
        _ = if x = 0 then
              {u : E | ‖u‖ ∈ prox[nonnegative_linear_penalty lam] 0}
            else
              (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_linear_penalty lam] ‖x‖ := hpiece
    rw [hprox]
    by_cases hx : x = 0
    · subst x
      have hzero_posPart : ((-lam)⁺ : ℝ) = 0 := by
        rw [posPart_eq_zero]
        linarith
      have hscalar0 : prox[nonnegative_linear_penalty lam] 0 = {0} := by
        have hscalar0' : prox[nonnegative_linear_penalty lam] 0 = {((-lam)⁺)} := by
          simpa [sub_eq_add_neg] using
            prox_nonnegative_linear_penalty_eq_singleton_posPart_sub lam 0
        simpa [hzero_posPart] using hscalar0'
      have hvector0 : {u : E | ‖u‖ ∈ prox[nonnegative_linear_penalty lam] 0} = {(0 : E)} := by
        ext u
        rw [hscalar0]
        simp
      simpa [max_eq_right (le_of_lt hlam)] using hvector0
    · rw [if_neg hx]
      have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hscalar :
          ((‖x‖ - lam)⁺ / ‖x‖ : ℝ) = 1 - lam / max ‖x‖ lam := by
        by_cases hle : ‖x‖ ≤ lam
        · rw [posPart_eq_zero.2 (sub_nonpos.mpr hle), zero_div, max_eq_right hle]
          rw [div_self (show lam ≠ 0 by linarith), sub_self]
        · have hlt : lam < ‖x‖ := lt_of_not_ge hle
          rw [posPart_eq_self.2 (sub_nonneg.mpr (le_of_lt hlt)), max_eq_left (le_of_lt hlt)]
          field_simp [hnorm_pos.ne']
      calc
        (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_linear_penalty lam] ‖x‖
            = {(((‖x‖ - lam)⁺ / ‖x‖) • x)} := by
                rw [prox_nonnegative_linear_penalty_eq_singleton_posPart_sub]
                simp
        _ = {(1 - lam / max ‖x‖ lam) • x} := by
              rw [Set.singleton_eq_singleton_iff]
              simp [hscalar]

-- Proof sketch: a singleton-valued proximal formula can be used directly as a membership
-- characterization by rewriting membership in `{y}` as equality to `y`.
/-- A vector belongs to `prox[norm_penalty lam] x` exactly when it equals the radial shrinkage
candidate from Example 6.19. -/
@[simp] theorem mem_prox_norm_penalty_iff
    (lam : ℝ) (hlam : 0 < lam) {x u : E} :
    u ∈ prox[norm_penalty lam] x ↔ u = (1 - lam / max ‖x‖ lam) • x := by
  rw [prox_norm_penalty_eq_singleton_shrinkage lam hlam x]
  simp

-- Proof sketch: in the branch `‖x‖ ≤ λ`, the `max` in the shrinkage factor is `λ`, so the
-- coefficient is `1 - λ / λ = 0`.
/-- If `‖x‖ ≤ λ`, then the proximal mapping of `x ↦ λ ‖x‖` collapses to the singleton `{0}`. -/
theorem prox_norm_penalty_eq_singleton_zero_of_norm_le
    (lam : ℝ) (hlam : 0 < lam) (x : E) (hx : ‖x‖ ≤ lam) :
    prox[norm_penalty lam] x = {(0 : E)} := by
  rw [prox_norm_penalty_eq_singleton_shrinkage lam hlam x, Set.singleton_eq_singleton_iff]
  rw [max_eq_right hx, div_self (show lam ≠ 0 by linarith), sub_self, zero_smul]

-- Proof sketch: in the branch `λ < ‖x‖`, the `max` in Example 6.19 is `‖x‖`, so the shrinkage
-- factor simplifies to the usual nonzero-ray coefficient `1 - λ / ‖x‖`.
/-- If `λ < ‖x‖`, then the proximal point is the usual nonzero radial shrinkage
`(1 - λ / ‖x‖) • x`. -/
theorem prox_norm_penalty_eq_singleton_shrinkage_of_lt_norm
    (lam : ℝ) (hlam : 0 < lam) (x : E) (hx : lam < ‖x‖) :
    prox[norm_penalty lam] x = {(1 - lam / ‖x‖) • x} := by
  simpa [max_eq_left (le_of_lt hx)] using prox_norm_penalty_eq_singleton_shrinkage lam hlam x

end

end
