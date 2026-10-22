/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_19
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProduct

universe u v

section

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/- Lemma 6.68 is `source-facing`: its owner is still the Chapter 6 proximal mapping `prox[...]`.
The mandatory domain sampling points to the following upstream owner abstractions.

1. `prox[...]` from Definition 6.1 is the chapter-level `core/canonical` proximal owner.
2. `ContinuousLinearMap.adjoint` with the scoped notation `†`, together with
   `ContinuousLinearMap.inverse` and `ContinuousLinearMap.IsInvertible`, is the canonical
   operator-theoretic owner surface in mathlib for the Gram operator `A A†`.
3. `proximal_mapping_precompose_continuousAffineMap` from Theorem 6.15 shows that this chapter's
   proximal transport API is organized around continuous linear or affine maps rather than
   coordinate models.
4. `norm_penalty` and `prox_norm_penalty_eq_singleton_shrinkage` from Example 6.19 identify the
   target-space penalty owner and its canonical proximal singleton formula.

Primitive data split by layer.
- `source-facing`: the continuous linear map `A`, the scalar `lam`, the base point `x`, and,
  when the textbook branch test is stated, the full-row-rank hypothesis on `A A†`.
- `bridge/view`: on the active branch, the proximal singleton formula only depends on a positive
  shift `α` satisfying `‖(A A† + α I)⁻¹ (A x)‖ = λ`; the global invertibility assumption belongs
  upstream in the existence theorem for that shift, not in the singleton formula itself.

The previous file stored a globally chosen shift as primitive public data. That was the wrong
layer: the positive multiplier only has mathematical meaning on the active branch. The refined API
keeps that multiplier branch-local through an existence/uniqueness theorem and a companion
proximal formula parameterized by any positive root. -/

section

variable (A : V →L[ℝ] W)

local notation "G" => A ∘L A†

/-- Helper for Lemma 6.68: every positive shift of the Gram operator `A A†` is invertible because
the spectrum of `A A†` is nonnegative. -/
lemma gram_shift_isInvertible_of_pos (α : ℝ) (hα : 0 < α) :
    (G + α • 1).IsInvertible := by
  -- The Gram operator is positive, so its spectrum stays in `[0, ∞)`.
  have hposG : (G).IsPositive := by
    simpa using ContinuousLinearMap.isPositive_self_comp_adjoint A
  have hnot : (-α) ∉ spectrum ℝ (G) := by
    intro hmem
    have hspec_nonneg : ∀ x ∈ spectrum ℝ (G), 0 ≤ x :=
      SpectrumRestricts.nnreal_iff.mp hposG.spectrumRestricts
    have hneg_nonneg : 0 ≤ -α := hspec_nonneg (-α) hmem
    linarith
  have hunit : IsUnit (G + α • 1) := by
    -- Passing to `-G` turns the positive shift into an ordinary resolvent condition.
    have hres : α ∉ spectrum ℝ (-G) := by
      intro hmem
      have hmem' : -α ∈ spectrum ℝ (G) := by
        rw [← spectrum.neg_eq] at hmem
        simpa [Set.mem_neg] using hmem
      exact hnot hmem'
    simpa [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc] using hres
  rcases hunit with ⟨u, hu⟩
  rw [← hu]
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ W u, rfl⟩

/-- Helper for Lemma 6.68: nonnegative shifts of `-A A†` lie in the resolvent set. At `0` this is
the given invertibility of `A A†`; for positive shifts it is the previous spectral lemma. -/
lemma gram_neg_mem_resolventSet_of_nonneg
    (hG : (G).IsInvertible) {α : ℝ} (hα : 0 ≤ α) :
    α ∈ resolventSet ℝ (-G) := by
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_comm]
  by_cases hzero : α = 0
  · -- At the endpoint `α = 0`, resolvent membership is just invertibility of `G`.
    subst hzero
    have hunit : IsUnit (G) := by
      rcases hG with ⟨e, he⟩
      rw [← he]
      exact e.toUnit.isUnit
    simpa using hunit
  · -- For strictly positive shifts, use the positive-spectrum exclusion.
    have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hzero)
    have hposG : (G).IsPositive := by
      simpa using ContinuousLinearMap.isPositive_self_comp_adjoint A
    have hnot : (-α) ∉ spectrum ℝ (G) := by
      intro hmem
      have hspec_nonneg : ∀ x ∈ spectrum ℝ (G), 0 ≤ x :=
        SpectrumRestricts.nnreal_iff.mp hposG.spectrumRestricts
      have hneg_nonneg : 0 ≤ -α := hspec_nonneg (-α) hmem
      linarith
    have hres : α ∉ spectrum ℝ (-G) := by
      intro hmem
      have hmem' : -α ∈ spectrum ℝ (G) := by
        rw [← spectrum.neg_eq] at hmem
        simpa [Set.mem_neg] using hmem
      exact hnot hmem'
    simpa [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_comm] using
      hres

/-- Helper for Lemma 6.68: the squared resolvent norm has an explicit derivative on
`[0, ∞)`. This packages the resolvent derivative theorem into the Gram-operator notation used in
the textbook proof. -/
lemma gram_shift_inverse_norm_sq_hasDerivAt
    (hG : (G).IsInvertible) (x : V) {α : ℝ} (hα : 0 ≤ α) :
    HasDerivAt (fun t : ℝ => ‖(G + t • 1).inverse (A x)‖ ^ 2)
      (-2 * inner ℝ ((G + α • 1).inverse (A x))
        ((G + α • 1).inverse ((G + α • 1).inverse (A x)))) α := by
  have hk : α ∈ resolventSet ℝ (-G) :=
    gram_neg_mem_resolventSet_of_nonneg (A := A) hG hα
  -- Differentiate the operator-valued resolvent, then evaluate it at `A x`.
  have hres :
      HasDerivAt (fun t : ℝ => resolvent (-G) t) (-(resolvent (-G) α ^ 2)) α :=
    spectrum.hasDerivAt_resolvent_const_left hk
  have happly :
      HasDerivAt (fun t : ℝ => resolvent (-G) t (A x))
        (-(resolvent (-G) α ^ 2) (A x)) α := by
    simpa using hres.clm_apply (hasDerivAt_const α (A x))
  have hsq :
      HasDerivAt (fun t : ℝ => ‖resolvent (-G) t (A x)‖ ^ 2)
        (2 * inner ℝ (resolvent (-G) α (A x)) ((-(resolvent (-G) α ^ 2)) (A x))) α :=
    happly.norm_sq
  simpa [pow_two, resolvent, Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_comm,
    ContinuousLinearMap.ringInverse_eq_inverse, mul_assoc] using hsq

/-- Helper for Lemma 6.68: on the positive half-line, the derivative of the squared resolvent norm
is strictly negative whenever `A x ≠ 0`. This is the strict-decrease mechanism behind the active
branch multiplier. -/
lemma gram_shift_inverse_norm_sq_deriv_neg
    (x : V) (hx : A x ≠ 0) {α : ℝ} (hα : 0 < α) :
    -2 * inner ℝ ((G + α • 1).inverse (A x))
      ((G + α • 1).inverse ((G + α • 1).inverse (A x))) < 0 := by
  let y := (G + α • 1).inverse (A x)
  let T : W →L[ℝ] W := G + α • 1
  have hshift : T.IsInvertible := by
    simpa [T] using gram_shift_isInvertible_of_pos (A := A) α hα
  have hy_ne : y ≠ 0 := by
    -- If the resolvent value vanished, applying the shift would force `A x = 0`.
    intro hy
    have hAx : A x = 0 := by
      simpa [y, T, hy] using (hshift.self_apply_inverse (A x)).symm
    exact hx hAx
  let z := T.inverse y
  have hz_ne : z ≠ 0 := by
    -- Invertibility also propagates nonvanishing one step further.
    intro hz
    apply hy_ne
    simpa [z, hz] using (hshift.self_apply_inverse y).symm
  have hposG : (G).IsPositive := by
    simpa using ContinuousLinearMap.isPositive_self_comp_adjoint A
  have hinner_pos : 0 < inner ℝ y z := by
    -- Rewrite `y = T z` and use positivity of `G` plus the strictly positive `α‖z‖²` term.
    have hz_eq : y = T z := by
      simpa [z] using (hshift.self_apply_inverse y).symm
    have hα_inner : inner ℝ ((α • (1 : W →L[ℝ] W)) z) z = α * ‖z‖ ^ 2 := by
      calc
        inner ℝ ((α • (1 : W →L[ℝ] W)) z) z = inner ℝ (α • z) z := by simp
        _ = α * inner ℝ z z := by rw [real_inner_smul_left]
        _ = α * ‖z‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    calc
      0 < α * ‖z‖ ^ 2 := by
        have hz_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
        positivity
      _ = inner ℝ ((α • (1 : W →L[ℝ] W)) z) z := by rw [hα_inner]
      _ ≤ inner ℝ (G z) z + inner ℝ ((α • (1 : W →L[ℝ] W)) z) z := by
        nlinarith [hposG.inner_nonneg_left z]
      _ = inner ℝ y z := by
        rw [hz_eq]
        simp [T, inner_add_left]
  have hfinal : -2 * inner ℝ y z < 0 := by
    nlinarith
  simpa [y, z, T] using hfinal

/-- Helper for Lemma 6.68: the map
`α ↦ ‖(A A† + α I)⁻¹ (A x)‖²` is strictly decreasing on `[0, ∞)` when `A x ≠ 0`. -/
lemma gram_shift_inverse_norm_sq_strictAntiOn_nonneg
    (hG : (G).IsInvertible) (x : V) (hx : A x ≠ 0) :
    StrictAntiOn (fun α : ℝ => ‖(G + α • 1).inverse (A x)‖ ^ 2) (Set.Ici 0) := by
  let f : ℝ → ℝ := fun α => ‖(G + α • 1).inverse (A x)‖ ^ 2
  let f' : ℝ → ℝ := fun α =>
    -2 * inner ℝ ((G + α • 1).inverse (A x))
      ((G + α • 1).inverse ((G + α • 1).inverse (A x)))
  have hcont : ContinuousOn f (Set.Ici 0) := by
    intro α hα
    exact (gram_shift_inverse_norm_sq_hasDerivAt (A := A) hG x hα).continuousAt.continuousWithinAt
  have hderiv :
      ∀ α ∈ interior (Set.Ici (0 : ℝ)),
        HasDerivWithinAt f (f' α) (interior (Set.Ici 0)) α := by
    intro α hα
    have hα' : 0 < α := by
      simpa using hα
    exact (gram_shift_inverse_norm_sq_hasDerivAt (A := A) hG x hα'.le).hasDerivWithinAt
  have hneg : ∀ α ∈ interior (Set.Ici (0 : ℝ)), f' α < 0 := by
    intro α hα
    have hα' : 0 < α := by
      simpa using hα
    exact gram_shift_inverse_norm_sq_deriv_neg (A := A) x hx hα'
  simpa [f, f'] using
    strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici (0 : ℝ)) hcont hderiv hneg

/-- Helper for Lemma 6.68: the shifted resolvent satisfies the elementary tail estimate
`‖(A A† + α I)⁻¹ (A x)‖ ≤ ‖A x‖ / α`. This is the large-`α` decay used in the active-branch
existence argument. -/
lemma gram_shift_inverse_norm_le_div (x : V) (α : ℝ) (hα : 0 < α) :
    ‖(G + α • 1).inverse (A x)‖ ≤ ‖A x‖ / α := by
  let y := (G + α • 1).inverse (A x)
  have hshift : (G + α • 1).IsInvertible :=
    gram_shift_isInvertible_of_pos (A := A) α hα
  have hposG : (G).IsPositive := by
    simpa using ContinuousLinearMap.isPositive_self_comp_adjoint A
  have hEq : G y + α • y = A x := by
    simpa [y, ContinuousLinearMap.add_apply] using hshift.self_apply_inverse (A x)
  by_cases hy : y = 0
  · -- The zero case is immediate because the right-hand side is nonnegative.
    have hnonneg : 0 ≤ ‖A x‖ / α := by
      positivity
    simpa [y, hy] using hnonneg
  · -- Otherwise compare `α‖y‖²` with `⟪A x, y⟫` and then divide by `α‖y‖ > 0`.
    have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hbound : α * ‖y‖ ^ 2 ≤ ‖A x‖ * ‖y‖ := by
      calc
        α * ‖y‖ ^ 2 ≤ inner ℝ (G y) y + α * ‖y‖ ^ 2 := by
          nlinarith [hposG.inner_nonneg_left y]
        _ = inner ℝ (A x) y := by
          rw [← hEq, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
        _ ≤ ‖A x‖ * ‖y‖ := real_inner_le_norm _ _
    have hmul : α * ‖y‖ ≤ ‖A x‖ := by
      nlinarith
    exact (le_div_iff₀ hα).2 <| by simpa [y, mul_comm] using hmul

/-- Helper for Lemma 6.68: the inactive-branch candidate kills the image under `A`. -/
lemma gram_inverse_candidate_apply (hG : (G).IsInvertible) (x : V) :
    A (x - (A†) ((G).inverse (A x))) = 0 := by
  -- Evaluate `A A† (A A†)⁻¹ (A x) = A x`, then subtract.
  have happly : A ((A†) ((G).inverse (A x))) = A x := by
    change (G) ((G).inverse (A x)) = A x
    simpa using hG.self_apply_inverse (A x)
  calc
    A (x - (A†) ((G).inverse (A x))) = A x - A ((A†) ((G).inverse (A x))) := by
      simp
    _ = 0 := by
      rw [happly, sub_self]

/-- Helper for Lemma 6.68: the active-branch candidate has image `α y`, where
`y = (A A† + α I)⁻¹ (A x)`. -/
lemma gram_shift_candidate_apply (α : ℝ) (hα : 0 < α) (x : V) :
    A (x - (A†) ((G + α • 1).inverse (A x))) = α • ((G + α • 1).inverse (A x)) := by
  let y := (G + α • 1).inverse (A x)
  have hshift : (G + α • 1).IsInvertible :=
    gram_shift_isInvertible_of_pos (A := A) α hα
  -- Rewrite the shifted inverse equation as `A x = G y + α y`.
  have hEq : G y + α • y = A x := by
    simpa [y, ContinuousLinearMap.add_apply] using hshift.self_apply_inverse (A x)
  calc
    A (x - (A†) y) = A x - G y := by
      simp [y]
    _ = (G y + α • y) - G y := by
      rw [hEq]
    _ = α • y := by
      abel

/-- Helper for Lemma 6.68: if the unshifted inverse norm is larger than a positive threshold,
then `A x` cannot vanish. -/
lemma linear_image_ne_zero_of_large_inverse_norm
    (lam : ℝ) (hlam : 0 < lam) (x : V)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    A x ≠ 0 := by
  -- Vanishing of `A x` would force the inverse image to be `0`, contradicting `lam > 0`.
  intro hAx
  have hzero : (G).inverse (A x) = 0 := by
    simp [hAx]
  have : lam < 0 := by
    simpa [hzero] using hlarge
  linarith

/-- Helper for Lemma 6.68: once the shift exceeds `‖A x‖ / λ`, the squared resolvent norm drops
below `λ²`. -/
lemma gram_shift_inverse_norm_sq_lt_sq_of_large_shift
    (lam : ℝ) (x : V) (hlam : 0 < lam) {α : ℝ}
    (hlarge : ‖A x‖ / lam < α) :
    ‖(G + α • 1).inverse (A x)‖ ^ 2 < lam ^ 2 := by
  have hdiv_nonneg : 0 ≤ ‖A x‖ / lam := by
    positivity
  have hα : 0 < α := lt_of_le_of_lt hdiv_nonneg hlarge
  have hnorm_lt : ‖(G + α • 1).inverse (A x)‖ < lam := by
    refine lt_of_le_of_lt (gram_shift_inverse_norm_le_div (A := A) x α hα) ?_
    refine (div_lt_iff₀ hα).2 ?_
    have hmul : ‖A x‖ < α * lam := by
      exact (div_lt_iff₀ hlam).1 hlarge
    simpa [mul_comm] using hmul
  -- Squaring preserves the strict inequality because both sides are nonnegative.
  nlinarith [hnorm_lt, norm_nonneg ((G + α • 1).inverse (A x)), hlam.le]

/-- Helper for Lemma 6.68: on the nonnegative half-line, a level strictly between the endpoint
values of the squared resolvent norm is attained at a unique positive shift. -/
lemma gram_shift_inverse_norm_sq_root_exists_unique
    (hG : (G).IsInvertible)
    (lam : ℝ) (x : V) (hx : A x ≠ 0)
    (h0 : lam ^ 2 < ‖(G).inverse (A x)‖ ^ 2)
    {R : ℝ} (hR : 0 < R)
    (hRlt : ‖(G + R • 1).inverse (A x)‖ ^ 2 < lam ^ 2) :
    ∃! α : ℝ,
      0 < α ∧
        ‖(G + α • 1).inverse (A x)‖ ^ 2 = lam ^ 2 := by
  let f : ℝ → ℝ := fun α => ‖(G + α • 1).inverse (A x)‖ ^ 2
  have hcont : ContinuousOn f (Set.Icc 0 R) := by
    -- The derivative formula gives continuity at every nonnegative point of the interval.
    intro t ht
    exact
      (gram_shift_inverse_norm_sq_hasDerivAt (A := A) hG x ht.1).continuousAt.continuousWithinAt
  have hmem : lam ^ 2 ∈ Set.Icc (f R) (f 0) := by
    -- The chosen level sits strictly between the right and left endpoint values.
    constructor
    · exact hRlt.le
    · simpa [f] using h0.le
  rcases (intermediate_value_Icc' hR.le hcont) hmem with ⟨α, hαIcc, hαeq⟩
  have hαne : α ≠ 0 := by
    -- A root at `0` would contradict the strict left endpoint inequality.
    intro hα0
    subst hα0
    have : lam ^ 2 < lam ^ 2 := by
      calc
        lam ^ 2 < ‖(G).inverse (A x)‖ ^ 2 := h0
        _ = lam ^ 2 := by simpa [f] using hαeq
    linarith
  have hαpos : 0 < α := by
    exact lt_of_le_of_ne hαIcc.1 (by simpa using hαne.symm)
  refine ⟨α, ?_, ?_⟩
  · exact ⟨hαpos, by simpa [f] using hαeq⟩
  · intro β hβ
    have hanti := gram_shift_inverse_norm_sq_strictAntiOn_nonneg (A := A) hG x hx
    have hβeq : β = α := by
      -- Strict decrease on `[0, ∞)` identifies the root uniquely.
      exact
        (hanti.eq_iff_eq (show α ∈ Set.Ici (0 : ℝ) from hαpos.le)
          (show β ∈ Set.Ici (0 : ℝ) from hβ.1.le)).1 <| by
            calc
              f α = lam ^ 2 := by simpa [f] using hαeq
              _ = f β := by simpa [f] using hβ.2.symm
    exact hβeq

/-- Helper for Lemma 6.68: for a positive target level, the norm equation is equivalent to the
corresponding squared norm equation. -/
lemma gram_shift_inverse_norm_eq_iff_sq_eq
    (lam : ℝ) (hlam : 0 < lam) (x : V) (α : ℝ) :
    ‖(G + α • 1).inverse (A x)‖ = lam ↔
      ‖(G + α • 1).inverse (A x)‖ ^ 2 = lam ^ 2 := by
  constructor
  · -- The forward direction is immediate by squaring both sides.
    intro h
    simp [h]
  · -- Nonnegativity of both sides lets us recover the norm equality from the squared one.
    intro hsq
    nlinarith [hsq, norm_nonneg ((G + α • 1).inverse (A x)), hlam.le]

/-- Lemma 6.68, active branch: if `A A†` is invertible and
`λ < ‖(A A†)⁻¹ (A x)‖`, then there is a unique positive shift `α` solving
`‖(A A† + α I)⁻¹ (A x)‖ = λ`. This is the branch-local multiplier from the textbook KKT
description; it is not promoted to a global chosen definition. -/
theorem existsUnique_linear_image_norm_prox_shift
    (hG : (G).IsInvertible)
    (lam : ℝ) (hlam : 0 < lam) (x : V)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    ∃! α : ℝ,
      0 < α ∧
        ‖(G + α • 1).inverse (A x)‖ = lam := by
  -- Route correction: package the scalar IVT argument at the squared-norm level first, and only
  -- then transport back to the norm equation required by the statement.
  have hx : A x ≠ 0 := by
    -- The active branch is impossible when the linear image vanishes.
    exact linear_image_ne_zero_of_large_inverse_norm (A := A) lam hlam x hlarge
  have h0 : lam ^ 2 < ‖(G).inverse (A x)‖ ^ 2 := by
    -- Squaring preserves the strict inequality because both sides are nonnegative.
    nlinarith [hlarge, norm_nonneg ((G).inverse (A x)), hlam.le]
  let R : ℝ := ‖A x‖ / lam + 1
  have hR : 0 < R := by
    -- The explicit endpoint is strictly positive and lies past the decay threshold.
    dsimp [R]
    positivity
  have hRlarge : ‖A x‖ / lam < R := by
    dsimp [R]
    linarith
  have hRlt : ‖(G + R • 1).inverse (A x)‖ ^ 2 < lam ^ 2 := by
    -- The tail bound places the right endpoint below the target level.
    exact gram_shift_inverse_norm_sq_lt_sq_of_large_shift (A := A) lam x hlam hRlarge
  rcases
      gram_shift_inverse_norm_sq_root_exists_unique (A := A) hG lam x hx h0 hR hRlt with
    ⟨α, hαsq, hαuniq⟩
  refine ⟨α, ?_, ?_⟩
  · -- Convert the unique squared root back to the norm equation from the statement.
    exact ⟨hαsq.1, (gram_shift_inverse_norm_eq_iff_sq_eq (A := A) lam hlam x α).2 hαsq.2⟩
  · intro β hβ
    -- Any other positive norm root gives the same squared root, hence the same shift.
    exact hαuniq β ⟨hβ.1, (gram_shift_inverse_norm_eq_iff_sq_eq (A := A) lam hlam x β).1 hβ.2⟩

-- Proof sketch: on the branch
-- `‖(A A†)⁻¹ (A x)‖ ≤ λ`, the KKT multiplier is `0`, so the proximal point is the affine
-- correction `x - A† (A A†)⁻¹ (A x)`.
/-- Lemma 6.68, inactive branch: if `A A†` is invertible and
`‖(A A†)⁻¹ (A x)‖ ≤ λ`, then the proximal set of `norm_penalty lam ∘ A` at `x` is the singleton
`{x - A† (A A†)⁻¹ (A x)}`. The textbook matrix formula is recovered by specializing
`V = ℝⁿ`, `W = ℝᵐ`, and `A` to a matrix linear map. -/
theorem prox_linear_image_norm_eq_singleton_of_le
    (hG : (G).IsInvertible)
    (lam : ℝ) (x : V)
    (hsmall : ‖(G).inverse (A x)‖ ≤ lam) :
    prox[norm_penalty lam ∘ A] x =
      {x - (A†) ((G).inverse (A x))} := by
  let y := (G).inverse (A x)
  let u := x - (A†) y
  have hproper : IsProperExtendedRealFunction (norm_penalty lam ∘ A) := by
    -- The penalty is finite everywhere, so the effective domain is all of `V`.
    refine ⟨?_, ?_⟩
    · intro z
      rw [Function.comp_apply, norm_penalty_apply]
      exact EReal.coe_ne_bot _
    · refine ⟨u, ?_⟩
      rw [mem_effective_domain, Function.comp_apply, norm_penalty_apply]
      simpa using (EReal.coe_lt_top (lam * ‖A u‖ : ℝ))
  refine prox_eq_singleton_of_effective_domain_and_inner_support
    (norm_penalty lam ∘ A) hproper x u ?_ ?_
  · -- The candidate lies in the effective domain because the objective is finite everywhere.
    rw [mem_effective_domain, Function.comp_apply, norm_penalty_apply]
    simpa using (EReal.coe_lt_top (lam * ‖A u‖ : ℝ))
  · intro v hv
    have hsmall' : ‖y‖ ≤ lam := by
      simpa [y] using hsmall
    have hu_apply : A u = 0 := by
      simpa [u, y] using gram_inverse_candidate_apply (A := A) hG x
    have hinner_eq : inner ℝ (x - u) (v - u) = inner ℝ y (A v) := by
      -- Move the adjoint across the inner product and use `A u = 0`.
      calc
        inner ℝ (x - u) (v - u) = inner ℝ ((A†) y) (v - u) := by
          simp [u]
        _ = inner ℝ y (A (v - u)) := by
          rw [ContinuousLinearMap.adjoint_inner_left]
        _ = inner ℝ y (A v) := by
          rw [map_sub, hu_apply, sub_zero]
    have hreal : inner ℝ (x - u) (v - u) ≤ lam * ‖A v‖ := by
      -- The support inequality is just Cauchy-Schwarz with `‖y‖ ≤ λ`.
      rw [hinner_eq]
      calc
        inner ℝ y (A v) ≤ ‖y‖ * ‖A v‖ := real_inner_le_norm _ _
        _ ≤ lam * ‖A v‖ := by gcongr
    rw [Function.comp_apply, Function.comp_apply, norm_penalty_apply, norm_penalty_apply,
      hu_apply, norm_zero, mul_zero]
    change (((inner ℝ (x - u) (v - u) : ℝ)) : EReal) ≤
      (((lam * ‖A v‖ : ℝ)) : EReal) - (((0 : ℝ)) : EReal)
    calc
      (((inner ℝ (x - u) (v - u) : ℝ)) : EReal) ≤ (((lam * ‖A v‖ : ℝ)) : EReal) :=
        EReal.coe_le_coe hreal
      _ = (((lam * ‖A v‖ : ℝ)) : EReal) - (((0 : ℝ)) : EReal) := by
        simp

-- Proof sketch: solve the proximal optimality system for `u ↦ λ ‖A u‖ + (1 / 2) ‖u - x‖²`.
-- On the active branch, any positive root `α` of `‖(A A† + α I)⁻¹ (A x)‖ = λ` produces the
-- proximal point `x - A† (A A† + α I)⁻¹ (A x)`. Combined with
-- `existsUnique_linear_image_norm_prox_shift`, this recovers the textbook unique active-branch
-- formula without introducing a global choice operator into the public API.
/-- Lemma 6.68, active branch proximal formula: if an explicit positive shift `α` satisfies
`‖(A A† + α I)⁻¹ (A x)‖ = λ`, then the proximal set of `norm_penalty lam ∘ A` at `x` is the
singleton `{x - A† (A A† + α I)⁻¹ (A x)}`. Together with
`existsUnique_linear_image_norm_prox_shift`, this is the canonical branch-local replacement for
the old piecewise formula with a globally chosen shift; the global full-row-rank assumption is
needed for existence of such an `α`, not for this branch-local singleton identity itself. -/
theorem prox_linear_image_norm_eq_singleton_of_shift
    (lam : ℝ) (x : V) (α : ℝ)
    (hα : 0 < α)
    (hroot : ‖(G + α • 1).inverse (A x)‖ = lam) :
    prox[norm_penalty lam ∘ A] x =
      {x - (A†) ((G + α • 1).inverse (A x))} := by
  let y := (G + α • 1).inverse (A x)
  let u := x - (A†) y
  have hproper : IsProperExtendedRealFunction (norm_penalty lam ∘ A) := by
    -- As in the inactive branch, the composed norm penalty is finite everywhere.
    refine ⟨?_, ?_⟩
    · intro z
      rw [Function.comp_apply, norm_penalty_apply]
      exact EReal.coe_ne_bot _
    · refine ⟨u, ?_⟩
      rw [mem_effective_domain, Function.comp_apply, norm_penalty_apply]
      simpa using (EReal.coe_lt_top (lam * ‖A u‖ : ℝ))
  refine prox_eq_singleton_of_effective_domain_and_inner_support
    (norm_penalty lam ∘ A) hproper x u ?_ ?_
  · -- The active-branch candidate is again automatically feasible for the effective domain.
    rw [mem_effective_domain, Function.comp_apply, norm_penalty_apply]
    simpa using (EReal.coe_lt_top (lam * ‖A u‖ : ℝ))
  · intro v hv
    have hy_norm : ‖y‖ = lam := by
      simpa [y] using hroot
    have hu_apply : A u = α • y := by
      simpa [u, y] using gram_shift_candidate_apply (A := A) α hα x
    have hinner_eq :
        inner ℝ (x - u) (v - u) = inner ℝ y (A v) - α * ‖y‖ ^ 2 := by
      -- The active candidate contributes the extra `α y` term in the image equation.
      calc
        inner ℝ (x - u) (v - u) = inner ℝ ((A†) y) (v - u) := by
          simp [u]
        _ = inner ℝ y (A (v - u)) := by
          rw [ContinuousLinearMap.adjoint_inner_left]
        _ = inner ℝ y (A v - α • y) := by
          rw [map_sub, hu_apply]
        _ = inner ℝ y (A v) - α * ‖y‖ ^ 2 := by
          rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hreal : inner ℝ (x - u) (v - u) ≤ lam * ‖A v‖ - lam * ‖A u‖ := by
      -- After rewriting `A u = α y`, the same Cauchy-Schwarz estimate closes the branch.
      calc
        inner ℝ (x - u) (v - u) = inner ℝ y (A v) - α * ‖y‖ ^ 2 := hinner_eq
        _ ≤ ‖y‖ * ‖A v‖ - α * ‖y‖ ^ 2 := by
          gcongr
          exact real_inner_le_norm _ _
        _ = lam * ‖A v‖ - α * lam ^ 2 := by
          rw [hy_norm]
        _ = lam * ‖A v‖ - lam * ‖A u‖ := by
          rw [hu_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hα, hy_norm]
          ring
    rw [Function.comp_apply, Function.comp_apply, norm_penalty_apply, norm_penalty_apply]
    change (((inner ℝ (x - u) (v - u) : ℝ)) : EReal) ≤
      (((lam * ‖A v‖ : ℝ)) : EReal) - (((lam * ‖A u‖ : ℝ)) : EReal)
    exact EReal.coe_le_coe hreal

end

end
