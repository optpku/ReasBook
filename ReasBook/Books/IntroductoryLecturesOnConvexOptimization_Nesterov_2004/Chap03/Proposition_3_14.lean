/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped BigOperators Pointwise RealInnerProductSpace WithTopConvexAnalysis

universe u v

variable {ι : Type u} {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Proposition 3.14 lies in the chapter's convex-subdifferential / finite absolute-inner-sum
domain.

The source-faithful route is:
1. rewrite `y ↦ ∑ i ∈ s, |⟪a i, y⟫|` as the finite supremum over all sign patterns;
2. identify each signed slice as a linear functional with singleton subdifferential;
3. compute the convex hull of the active signed sums as the fixed positive/negative base plus the
   zero-coordinate segment sum.

This file keeps that route explicit. The remaining blocker is not the mathematical skeleton but the
attach-indexed finite-sum normalization needed to pass from active sign patterns to the displayed
surface formula. -/

/-- Helper for Proposition 3.14: a sign choice on the finite index family `s`. -/
abbrev SignPattern (s : Finset ι) :=
  s → Bool

/-- Helper for Proposition 3.14: the signed vector sum attached to a sign pattern. -/
abbrev signedVectorSum (s : Finset ι) (a : ι → V) (σ : SignPattern s) : V :=
  ∑ i : s, if σ i then a i.1 else -a i.1

/-- Helper for Proposition 3.14: the linear slice corresponding to a sign pattern. -/
abbrev signedSlice (s : Finset ι) (a : ι → V) (σ : SignPattern s) (y : V) : ℝ :=
  ∑ i : s, if σ i then ⟪a i.1, y⟫ else -⟪a i.1, y⟫

/-- Helper for Proposition 3.14: each signed scalar term is bounded above by the corresponding
absolute value. -/
lemma signed_term_le_abs (b : Bool) (t : ℝ) :
    (if b then t else -t) ≤ |t| := by
  by_cases hb : b
  · simp [hb, le_abs_self]
  · simp [hb, neg_le_abs]

/-- Helper for Proposition 3.14: a signed slice is the inner product against its signed vector
sum. -/
lemma signedSlice_eq_inner_signedVectorSum
    (s : Finset ι) (a : ι → V) (σ : SignPattern s) :
    signedSlice s a σ = fun y ↦ inner ℝ (signedVectorSum s a σ) y := by
  funext y
  -- Repackage the finite signed sum as one linear functional.
  rw [signedSlice, signedVectorSum, sum_inner]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hσ : σ i
  · simp [hσ]
  · simp [hσ, inner_neg_left]

/-- Helper for Proposition 3.14: a sum over the subtype `s` can be rewritten as a surface sum over
`s` by extending the summand with `0` off the finite set. -/
lemma sum_subtype_eq_sum_surface
    [DecidableEq ι] {W : Type*} [AddCommMonoid W]
    (s : Finset ι) (F : s → W) :
    (∑ i : s, F i) = ∑ j ∈ s, if h : j ∈ s then F ⟨j, h⟩ else 0 := by
  -- Normalize the subtype sum through `s.attach`, then collapse the attach proof.
  rw [Finset.univ_eq_attach]
  simpa using
    (Finset.sum_attach (s := s)
      (f := fun j ↦ if h : j ∈ s then F ⟨j, h⟩ else 0))

/-- Helper for Proposition 3.14: the signed vector sum has a surface-sum presentation over `s`. -/
lemma signed_sum_eq_surface_sum
    [DecidableEq ι] (s : Finset ι) (a : ι → V) (σ : SignPattern s) :
    signedVectorSum s a σ =
      ∑ j ∈ s, if h : j ∈ s then if σ ⟨j, h⟩ then a j else -a j else 0 := by
  -- Specialize the generic subtype-to-surface bridge to the signed vector summand.
  simpa [signedVectorSum] using
    (sum_subtype_eq_sum_surface
      (s := s) (F := fun i ↦ if σ i then a i.1 else -a i.1))

/-- Helper for Proposition 3.14: the signed slice has a surface-sum presentation over `s`. -/
lemma signed_slice_eq_surface_sum
    [DecidableEq ι] (s : Finset ι) (a : ι → V) (σ : SignPattern s) (y : V) :
    signedSlice s a σ y =
      ∑ j ∈ s, if h : j ∈ s then if σ ⟨j, h⟩ then ⟪a j, y⟫ else -⟪a j, y⟫ else 0 := by
  -- The same normalization works for the scalar signed slice.
  simpa [signedSlice] using
    (sum_subtype_eq_sum_surface
      (s := s) (F := fun i ↦ if σ i then ⟪a i.1, y⟫ else -⟪a i.1, y⟫))

/-- Helper for Proposition 3.14: the absolute-value subtype sum equals the usual surface sum over
`s`. -/
lemma subtype_abs_inner_sum_eq_surface_sum
    (s : Finset ι) (a : ι → V) (y : V) :
    (∑ i : s, |⟪a i.1, y⟫|) = ∑ i ∈ s, |⟪a i, y⟫| := by
  -- Rewrite the subtype sum through `s.attach`, where the summand depends only on the ambient
  -- index and no longer on the membership proof.
  rw [Finset.univ_eq_attach]
  simpa using (Finset.sum_attach (s := s) (f := fun i ↦ |⟪a i, y⟫|))

/-- Helper for Proposition 3.14: the sign-pattern supremum route does produce the original
absolute-value sum. -/
lemma sum_abs_inner_eq_pointwiseSupremumOn_sign_patterns
    (s : Finset ι) (a : ι → V) :
    pointwiseSupremumOn (Set.univ : Set (SignPattern s))
        (fun y σ ↦ (signedSlice s a σ y : WithTop ℝ)) =
      fun y ↦ (((∑ i ∈ s, |⟪a i, y⟫|) : ℝ) : WithTop ℝ) := by
  classical
  let _ : Fintype (SignPattern s) := inferInstance
  let _ : Nonempty (SignPattern s) := ⟨fun _ ↦ false⟩
  funext y
  -- Evaluate the finite supremum at `y` and bound it termwise by the absolute-value sum.
  rw [pointwiseSupremumOn_univ_eq_sup' (ι := SignPattern s)]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le Finset.univ_nonempty
        (fun σ : SignPattern s ↦ (signedSlice s a σ y : WithTop ℝ)) ?_
    intro σ hσ
    have hreal : signedSlice s a σ y ≤ ∑ i : s, |⟪a i.1, y⟫| := by
      -- Each signed term is bounded above by the corresponding absolute value.
      rw [signedSlice]
      refine Finset.sum_le_sum ?_
      intro i hi
      exact signed_term_le_abs (σ i) ⟪a i.1, y⟫
    rw [subtype_abs_inner_sum_eq_surface_sum] at hreal
    exact show ((signedSlice s a σ y : ℝ) : WithTop ℝ) ≤
        (((∑ i ∈ s, |⟪a i, y⟫| : ℝ) : ℝ) : WithTop ℝ) from by
      exact_mod_cast hreal
  · let σ0 : SignPattern s := fun i ↦ decide (0 ≤ ⟪a i.1, y⟫)
    have hreal : signedSlice s a σ0 y = ∑ i : s, |⟪a i.1, y⟫| := by
      -- Choose the maximizing sign pattern given by the sign of each inner product.
      rw [signedSlice]
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hnonneg : 0 ≤ ⟪a i.1, y⟫
      · simp [σ0, hnonneg, abs_of_nonneg]
      · have hneg : ⟪a i.1, y⟫ < 0 := lt_of_not_ge hnonneg
        simp [σ0, hnonneg, abs_of_neg hneg]
    have hsurf :
        (signedSlice s a σ0 y : WithTop ℝ) =
          (((∑ i ∈ s, |⟪a i, y⟫| : ℝ) : ℝ) : WithTop ℝ) := by
      -- The maximizing subtype sum is the displayed surface sum.
      rw [hreal, subtype_abs_inner_sum_eq_surface_sum]
    rw [← hsurf]
    exact Finset.le_sup'
      (s := (Finset.univ : Finset (SignPattern s)))
      (f := fun σ : SignPattern s ↦ (signedSlice s a σ y : WithTop ℝ))
      (by simp [σ0])

/-- Helper for Proposition 3.14: a linear inner-product functional has singleton
subdifferential given by its coefficient vector. -/
lemma subdifferential_inner_eq_singleton (v x : V) :
    ∂ (fun y ↦ ((inner ℝ v y) : ℝ))(x) = {v} := by
  ext g
  rw [Set.mem_singleton_iff, mem_subdifferential_coe_real_iff]
  constructor
  · intro hg
    -- Test the subgradient inequality in the direction `g - v` to force the norm gap to vanish.
    have hz := hg (x + (g - v))
    have hineq : inner ℝ g (g - v) ≤ inner ℝ v (g - v) := by
      have hrewrite :
          inner ℝ v (x + (g - v)) = inner ℝ v x + inner ℝ v (g - v) := by
        rw [inner_add_right]
      have hsub : x + (g - v) - x = g - v := by
        abel_nf
      rw [hrewrite, hsub] at hz
      linarith
    have hnonpos : ‖g - v‖ ^ (2 : ℕ) ≤ 0 := by
      have hpair : inner ℝ (g - v) (g - v) ≤ 0 := by
        calc
          inner ℝ (g - v) (g - v) = inner ℝ g (g - v) - inner ℝ v (g - v) := by
            rw [inner_sub_left]
          _ ≤ 0 := sub_nonpos.mpr hineq
      simpa [real_inner_self_eq_norm_sq] using hpair
    have hzeroNorm : ‖g - v‖ = 0 := by
      nlinarith [sq_nonneg ‖g - v‖, hnonpos]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzeroNorm)
  · intro hg
    subst hg
    intro y
    -- For the true coefficient vector, the affine support inequality is an equality.
    have hy : y = x + (y - x) := by
      abel_nf
    have hsub : x + (y - x) - x = y - x := by
      abel_nf
    rw [hy, inner_add_right, hsub]

/-- Helper for Proposition 3.14: every signed slice has singleton subdifferential given by its
signed vector sum. -/
lemma subdifferential_signed_inner_slice_eq_singleton
    (s : Finset ι) (a : ι → V) (σ : SignPattern s) (x : V) :
    ∂ (fun y ↦ (signedSlice s a σ y : WithTop ℝ))(x) =
      {signedVectorSum s a σ} := by
  -- Rewrite the slice to the canonical linear form and apply the singleton computation.
  rw [signedSlice_eq_inner_signedVectorSum]
  simpa using subdifferential_inner_eq_singleton (signedVectorSum s a σ) x

/-- Helper for Proposition 3.14: equality in the scalar signed-term bound forces the expected sign
choice away from the zero case. -/
lemma signed_term_eq_abs_iff_sign_choice (b : Bool) (t : ℝ) :
    (if b then t else -t) = |t| ↔
      (0 < t → b = true) ∧ (t < 0 → b = false) := by
  constructor
  · intro h
    constructor
    · intro ht
      by_cases hb : b = true
      · exact hb
      · have hb' : b = false := by
          cases b <;> simp at hb ⊢
        have : -t = t := by simpa [hb', abs_of_pos ht] using h
        linarith
    · intro ht
      by_cases hb : b = true
      · have : t = -t := by simpa [hb, abs_of_neg ht] using h
        linarith
      · have hb' : b = false := by
          cases b <;> simp at hb ⊢
        exact hb'
  · rintro ⟨hpos, hneg⟩
    by_cases ht_pos : 0 < t
    · have hb : b = true := hpos ht_pos
      simp [hb, abs_of_pos ht_pos]
    · by_cases ht_neg : t < 0
      · have hb : b = false := hneg ht_neg
        simp [hb, abs_of_neg ht_neg]
      · have ht_zero : t = 0 := by linarith
        simp [ht_zero]

/-- Helper for Proposition 3.14: a finite Minkowski sum of symmetric two-point sets is exactly the
set of the corresponding signed surface sums. -/
lemma mem_sum_pairs_iff_exists_signed_sum
    (s : Finset ι) (a : ι → V) (z : V) :
    z ∈ s.sum (fun i ↦ ({-a i, a i} : Set V)) ↔
      ∃ ε : ι → Bool, z = ∑ i ∈ s, if ε i then a i else -a i := by
  classical
  induction s using Finset.induction_on generalizing z with
  | empty =>
      constructor
      · intro hz
        -- The empty Minkowski sum is `{0}`, so any witness sign function works.
        refine ⟨fun _ ↦ false, ?_⟩
        simpa using hz
      · rintro ⟨ε, hz⟩
        simp [hz]
  | @insert i s hi ih =>
      constructor
      · intro hz
        -- Peel off the `i`-th two-point contribution and apply the induction hypothesis.
        rw [Finset.sum_insert hi, Set.mem_add] at hz
        rcases hz with ⟨u, hu, w, hw, rfl⟩
        rcases (ih w).1 hw with ⟨ε, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl
        · let ε' : ι → Bool := Function.update ε i false
          have hs :
              (∑ j ∈ s, if ε' j then a j else -a j) =
                ∑ j ∈ s, if ε j then a j else -a j := by
            -- Off the inserted index, the updated sign function agrees with `ε`.
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hji : j ≠ i := by
              intro hji
              exact hi (by simpa [hji] using hj)
            simp [ε', hji]
          refine ⟨ε', ?_⟩
          rw [Finset.sum_insert hi, hs]
          simp [ε']
        · let ε' : ι → Bool := Function.update ε i true
          have hs :
              (∑ j ∈ s, if ε' j then a j else -a j) =
                ∑ j ∈ s, if ε j then a j else -a j := by
            -- The same update argument handles the positive sign choice.
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hji : j ≠ i := by
              intro hji
              exact hi (by simpa [hji] using hj)
            simp [ε', hji]
          refine ⟨ε', ?_⟩
          rw [Finset.sum_insert hi, hs]
          simp [ε']
      · rintro ⟨ε, rfl⟩
        -- Rebuild the Minkowski-sum witness from the current sign at `i` and the inductive tail.
        rw [Finset.sum_insert hi]
        refine Set.mem_add.2 ?_
        have hzsum :
            ((if ε i then a i else -a i) + ∑ j ∈ s, if ε j then a j else -a j) =
              ∑ j ∈ insert i s, if ε j then a j else -a j := by
          rw [Finset.sum_insert hi]
        refine ⟨if ε i then a i else -a i, ?_, ∑ j ∈ s, if ε j then a j else -a j, ?_, hzsum⟩
        · by_cases hε : ε i
          · simp [hε]
          · simp [hε]
        · exact (ih _).2 ⟨ε, rfl⟩

/-- Helper for Proposition 3.14: the signed-gap sum vanishes exactly when every coordinatewise
gap vanishes. -/
lemma surface_signed_gap_sum_eq_zero_iff
    (s : Finset ι) (a : ι → V) (x : V) (σ : SignPattern s) :
    (∑ i : s, (|⟪a i.1, x⟫| - (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫))) = 0 ↔
      ∀ i : s, |⟪a i.1, x⟫| - (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫) = 0 := by
  let gap : s → ℝ := fun i ↦ |⟪a i.1, x⟫| - (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫)
  have hnonneg : ∀ i ∈ (Finset.univ : Finset s), 0 ≤ gap i := by
    intro i hi
    dsimp [gap]
    exact sub_nonneg.mpr (signed_term_le_abs (σ i) ⟪a i.1, x⟫)
  -- The whole sum can be zero only if every nonnegative coordinate gap is zero.
  simpa [gap] using
    (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset s)) hnonneg)

/-- Helper for Proposition 3.14: once the positive and negative signs are fixed, the signed
surface sum splits into the positive base, the negative base, and the remaining zero-part
contribution. -/
lemma signed_surface_sum_decomposition
    (s : Finset ι) (a : ι → V) (x : V) (ε : ι → Bool)
    (hpos : ∀ i ∈ s, 0 < ⟪a i, x⟫ → ε i = true)
    (hneg : ∀ i ∈ s, ⟪a i, x⟫ < 0 → ε i = false) :
    ∑ i ∈ s, (if ε i then a i else -a i) =
      (s.filter fun i ↦ 0 < ⟪a i, x⟫).sum a -
        (s.filter fun i ↦ ⟪a i, x⟫ < 0).sum a +
          Finset.sum (s.filter (fun i ↦ ⟪a i, x⟫ = 0)) (fun i ↦ if ε i then a i else -a i) := by
  classical
  let pos : ι → Prop := fun i ↦ 0 < ⟪a i, x⟫
  let neg : ι → Prop := fun i ↦ ⟪a i, x⟫ < 0
  let term : ι → V := fun i ↦ if ε i then a i else -a i
  have hsplitPos :=
    (Finset.sum_filter_add_sum_filter_not s pos term).symm
  have hsplitNeg :=
    (Finset.sum_filter_add_sum_filter_not (s.filter fun i ↦ ¬ pos i) neg term).symm
  have hposSum : Finset.sum (s.filter pos) term = Finset.sum (s.filter pos) a := by
    -- On the positive coordinates the sign is forced to be `true`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hipos : 0 < ⟪a i, x⟫ := (Finset.mem_filter.mp hi).2
    have hε : ε i = true := hpos i his hipos
    simp [term, hε]
  have hnegFilter :
      (s.filter (fun i ↦ ¬ pos i)).filter neg = s.filter neg := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter] at hi
      rcases hi with ⟨hi₁, hneg'⟩
      rw [Finset.mem_filter] at hi₁
      rcases hi₁ with ⟨his, hnotPos⟩
      rw [Finset.mem_filter]
      exact ⟨his, hneg'⟩
    · intro hi
      rw [Finset.mem_filter] at hi ⊢
      rcases hi with ⟨his, hneg'⟩
      refine ⟨?_, hneg'⟩
      rw [Finset.mem_filter]
      refine ⟨his, ?_⟩
      linarith
  have hnegSum :
      Finset.sum ((s.filter (fun i ↦ ¬ pos i)).filter neg) term = -(Finset.sum (s.filter neg) a) := by
    rw [hnegFilter]
    calc
      Finset.sum (s.filter neg) term = Finset.sum (s.filter neg) (fun i ↦ -a i) := by
        -- On the negative coordinates the sign is forced to be `false`.
        refine Finset.sum_congr rfl ?_
        intro i hi
        have his : i ∈ s := (Finset.mem_filter.mp hi).1
        have hneg' : ⟪a i, x⟫ < 0 := (Finset.mem_filter.mp hi).2
        have hε : ε i = false := hneg i his hneg'
        simp [term, hε]
      _ = -(Finset.sum (s.filter neg) a) := by
        simp
  have hzeroFilter :
      (s.filter (fun i ↦ ¬ pos i)).filter (fun i ↦ ¬ neg i) =
        s.filter (fun i ↦ ⟪a i, x⟫ = 0) := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter] at hi
      rcases hi with ⟨hi₁, hnotNeg⟩
      rw [Finset.mem_filter] at hi₁
      rcases hi₁ with ⟨his, hnotPos⟩
      rw [Finset.mem_filter]
      exact ⟨his, by linarith⟩
    · intro hi
      rw [Finset.mem_filter] at hi ⊢
      rcases hi with ⟨his, hzero⟩
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨his, ?_⟩
        linarith [hzero]
      · linarith [hzero]
  -- Split the surface sum into positive, negative, and zero branches before simplifying each
  -- branch separately.
  calc
    Finset.sum s term
        = Finset.sum (s.filter pos) term + Finset.sum (s.filter fun i ↦ ¬ pos i) term := by
            simpa [pos, term] using hsplitPos
    _ = Finset.sum (s.filter pos) term +
          (Finset.sum ((s.filter (fun i ↦ ¬ pos i)).filter neg) term +
            Finset.sum ((s.filter (fun i ↦ ¬ pos i)).filter (fun i ↦ ¬ neg i)) term) := by
          rw [hsplitNeg]
    _ = Finset.sum (s.filter pos) a +
          (-(Finset.sum (s.filter neg) a) +
            Finset.sum (s.filter fun i ↦ ⟪a i, x⟫ = 0) term) := by
          rw [hposSum, hnegSum, hzeroFilter]
    _ = (s.filter fun i ↦ 0 < ⟪a i, x⟫).sum a -
          (s.filter fun i ↦ ⟪a i, x⟫ < 0).sum a +
            Finset.sum (s.filter (fun i ↦ ⟪a i, x⟫ = 0)) (fun i ↦ if ε i then a i else -a i) := by
          simp [pos, neg, term, sub_eq_add_neg, add_assoc]

/-- Helper for Proposition 3.14: an active sign pattern fixes the positive and negative
coordinates, while the zero coordinates remain free. -/
lemma mem_active_sign_pattern_iff
    (s : Finset ι) (a : ι → V) (x : V) (σ : SignPattern s) :
    σ ∈ activePointwiseSupremumOnIndices
          (Set.univ : Set (SignPattern s))
          (fun y τ ↦ (signedSlice s a τ y : WithTop ℝ))
          x ↔
      (∀ i : s, 0 < ⟪a i.1, x⟫ → σ i = true) ∧
        (∀ i : s, ⟪a i.1, x⟫ < 0 → σ i = false) := by
  rw [mem_activePointwiseSupremumOnIndices_univ_iff,
    sum_abs_inner_eq_pointwiseSupremumOn_sign_patterns]
  constructor
  · intro hσ
    have hsurfaceTop :
        ((signedSlice s a σ x : ℝ) : WithTop ℝ) =
          ((((∑ i ∈ s, |⟪a i, x⟫|) : ℝ) : ℝ) : WithTop ℝ) := by
      simpa using hσ
    have hsurface : signedSlice s a σ x = ∑ i ∈ s, |⟪a i, x⟫| := by
      exact_mod_cast hsurfaceTop
    have hsubtype : signedSlice s a σ x = ∑ i : s, |⟪a i.1, x⟫| := by
      rw [← subtype_abs_inner_sum_eq_surface_sum] at hsurface
      exact hsurface
    have hgapSum :
        (∑ i : s, (|⟪a i.1, x⟫| - (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫))) = 0 := by
      -- Activity means the total signed slice reaches the total absolute-value bound.
      have hsubtype' := hsubtype
      unfold signedSlice at hsubtype'
      rw [Finset.sum_sub_distrib, ← hsubtype']
      simp
    have hgap := (surface_signed_gap_sum_eq_zero_iff s a x σ).1 hgapSum
    constructor
    · intro i hiPos
      have hterm : (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫) = |⟪a i.1, x⟫| := by
        linarith [hgap i]
      exact ((signed_term_eq_abs_iff_sign_choice (σ i) ⟪a i.1, x⟫).1 hterm).1 hiPos
    · intro i hiNeg
      have hterm : (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫) = |⟪a i.1, x⟫| := by
        linarith [hgap i]
      exact ((signed_term_eq_abs_iff_sign_choice (σ i) ⟪a i.1, x⟫).1 hterm).2 hiNeg
  · rintro ⟨hpos, hneg⟩
    have hsubtype : signedSlice s a σ x = ∑ i : s, |⟪a i.1, x⟫| := by
      -- The sign constraints force equality in each scalar bound.
      rw [signedSlice]
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact (signed_term_eq_abs_iff_sign_choice (σ i) ⟪a i.1, x⟫).2
        ⟨hpos i, hneg i⟩
    have hsurface : signedSlice s a σ x = ∑ i ∈ s, |⟪a i, x⟫| := by
      rw [hsubtype, subtype_abs_inner_sum_eq_surface_sum]
    simpa using congrArg (fun t : ℝ ↦ ((t : ℝ) : WithTop ℝ)) hsurface

/-- Helper for Proposition 3.14: the active signed sums equal the fixed positive-minus-negative
base translated by the zero-coordinate sign choices. -/
lemma active_signed_sums_eq_base_add_zero_pairs
    (s : Finset ι) (a : ι → V) (x : V) :
    {g | ∃ σ : SignPattern s,
        σ ∈ activePointwiseSupremumOnIndices
              (Set.univ : Set (SignPattern s))
              (fun y τ ↦ (signedSlice s a τ y : WithTop ℝ))
              x ∧
          g = signedVectorSum s a σ} =
      ({(s.filter fun i ↦ 0 < ⟪a i, x⟫).sum a -
          (s.filter fun i ↦ ⟪a i, x⟫ < 0).sum a} : Set V) +
        (s.filter fun i ↦ ⟪a i, x⟫ = 0).sum (fun i ↦ ({-a i, a i} : Set V)) := by
  classical
  let base : V :=
    (s.filter fun i ↦ 0 < ⟪a i, x⟫).sum a -
      (s.filter fun i ↦ ⟪a i, x⟫ < 0).sum a
  let zeroSet : Finset ι := s.filter fun i ↦ ⟪a i, x⟫ = 0
  ext g
  constructor
  · rintro ⟨σ, hσactive, rfl⟩
    rcases (mem_active_sign_pattern_iff s a x σ).1 hσactive with ⟨hpos, hneg⟩
    let εσ : ι → Bool := fun i ↦ if h : i ∈ s then σ ⟨i, h⟩ else false
    have hsurface :
        signedVectorSum s a σ = ∑ i ∈ s, if εσ i then a i else -a i := by
      -- Extend the subtype sign pattern to an ambient surface sign choice.
      rw [signed_sum_eq_surface_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [εσ, hi]
    have hdecomp :=
      signed_surface_sum_decomposition s a x εσ
        (by
          intro i hi hiPos
          simpa [εσ, hi] using hpos ⟨i, hi⟩ hiPos)
        (by
          intro i hi hiNeg
          simpa [εσ, hi] using hneg ⟨i, hi⟩ hiNeg)
    have hzeroMem :
        (∑ i ∈ zeroSet, if εσ i then a i else -a i) ∈
          zeroSet.sum (fun i ↦ ({-a i, a i} : Set V)) := by
      exact (mem_sum_pairs_iff_exists_signed_sum
        (s := zeroSet) (a := a)
        (z := ∑ i ∈ zeroSet, if εσ i then a i else -a i)).2 ⟨εσ, rfl⟩
    have hsigned :
        signedVectorSum s a σ = base + ∑ i ∈ zeroSet, if εσ i then a i else -a i := by
      calc
        signedVectorSum s a σ = ∑ i ∈ s, if εσ i then a i else -a i := hsurface
        _ = base + ∑ i ∈ zeroSet, if εσ i then a i else -a i := by
          simpa [base, zeroSet, sub_eq_add_neg, add_assoc] using hdecomp
    refine Set.mem_add.2 ?_
    refine ⟨base, by simp [base], ∑ i ∈ zeroSet, if εσ i then a i else -a i, hzeroMem, ?_⟩
    exact hsigned.symm
  · intro hg
    rcases Set.mem_add.1 hg with ⟨b, hb, z, hz, hsum⟩
    have hb' : b = base := by
      simpa [base] using hb
    subst hb'
    rcases (mem_sum_pairs_iff_exists_signed_sum (s := zeroSet) (a := a) (z := z)).1 hz with
      ⟨ε0, hz0⟩
    let ε : ι → Bool := fun i ↦
      if hposi : 0 < ⟪a i, x⟫ then true else if hnegi : ⟪a i, x⟫ < 0 then false else ε0 i
    let σ : SignPattern s := fun i ↦ ε i.1
    have hσactive :
        σ ∈ activePointwiseSupremumOnIndices
              (Set.univ : Set (SignPattern s))
              (fun y τ ↦ (signedSlice s a τ y : WithTop ℝ))
              x := by
      rw [mem_active_sign_pattern_iff]
      constructor
      · intro i hiPos
        -- Positive coordinates are forced to the positive sign.
        simp [σ, ε, hiPos]
      · intro i hiNeg
        -- Negative coordinates are forced to the negative sign.
        have hnotPos : ¬ 0 < ⟪a i.1, x⟫ := by
          linarith
        simp [σ, ε, hnotPos, hiNeg]
    have hsurface :
        signedVectorSum s a σ = ∑ i ∈ s, if ε i then a i else -a i := by
      -- The subtype sign pattern and the ambient sign choice agree on `s`.
      rw [signed_sum_eq_surface_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [σ, ε, hi]
    have hdecomp :=
      signed_surface_sum_decomposition s a x ε
        (by
          intro i hi hiPos
          simp [ε, hiPos])
        (by
          intro i hi hiNeg
          have hnotPos : ¬ 0 < ⟪a i, x⟫ := by
            linarith
          simp [ε, hnotPos, hiNeg])
    have hzeroSum :
        (∑ i ∈ zeroSet, if ε i then a i else -a i) = z := by
      rw [hz0]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hzero : ⟪a i, x⟫ = 0 := (Finset.mem_filter.mp hi).2
      have hnotPos : ¬ 0 < ⟪a i, x⟫ := by
        linarith
      have hnotNeg : ¬ ⟪a i, x⟫ < 0 := by
        linarith
      simp [ε, hnotPos, hnotNeg]
    have hsigned : signedVectorSum s a σ = base + z := by
      calc
        signedVectorSum s a σ = ∑ i ∈ s, if ε i then a i else -a i := hsurface
        _ = base + ∑ i ∈ zeroSet, if ε i then a i else -a i := by
          simpa [base, zeroSet, sub_eq_add_neg, add_assoc] using hdecomp
        _ = base + z := by rw [hzeroSum]
    refine ⟨σ, hσactive, ?_⟩
    exact (hsigned.trans hsum).symm

/-- Helper for Proposition 3.14: each signed slice is a closed convex function. -/
lemma signed_slice_closedConvexFunction
    (s : Finset ι) (a : ι → V) (σ : SignPattern s) :
    ClosedConvexFunction (fun y ↦ (signedSlice s a σ y : WithTop ℝ)) := by
  -- Rewrite the slice to a linear functional and package convexity plus continuity.
  rw [signedSlice_eq_inner_signedVectorSum]
  apply closedConvexFunction_coe_of_convexOn_continuous
  · let L : V →ₗ[ℝ] ℝ :=
      { toFun := fun y ↦ inner ℝ (signedVectorSum s a σ) y
        map_add' := by
          intro y z
          rw [inner_add_right]
        map_smul' := by
          intro c y
          simpa [smul_eq_mul] using
            (inner_smul_right (signedVectorSum s a σ) y c) }
    -- Linear functionals are convex on the whole space.
    simpa using L.convexOn convex_univ
  · -- The inner-product pairing is continuous in its second argument.
    simpa using (continuous_const.inner continuous_id)

/-- Proposition 3.14: for `f(x) = ∑_{i ∈ s} |⟪aᵢ, x⟫|`, the subdifferential at `x` is the signed
sum of the active vectors with positive and negative inner products, translated by the Minkowski
sum of the symmetric line segments `[-aᵢ, aᵢ] = segment ℝ (-aᵢ) aᵢ` over the zero inner-product
indices. -/
-- Proof sketch: rewrite the function as the supremum over sign patterns, apply the finite
-- pointwise-supremum subdifferential theorem, rewrite each active slice subdifferential to a
-- singleton signed sum, and then replace the convex hull of active signed sums by the displayed
-- positive/negative base plus zero-index segment sum.
theorem subdifferential_sum_abs_inner_eq_signed_sum_add_zero_segments
    (s : Finset ι) (a : ι → V) (x : V) :
    ∂ (fun y ↦ ((∑ i ∈ s, |⟪a i, y⟫|) : ℝ))(x) =
      ({(s.filter fun i ↦ 0 < ⟪a i, x⟫).sum a -
          (s.filter fun i ↦ ⟪a i, x⟫ < 0).sum a} : Set V) +
        (s.filter fun i ↦ ⟪a i, x⟫ = 0).sum (fun i ↦ segment ℝ (-a i) (a i)) := by
  -- Route correction: the source proof runs through the finite sign-pattern supremum, not through
  -- the earlier support-function theorem with nonnegative multipliers.
  classical
  let _ : Fintype (SignPattern s) := inferInstance
  let _ : Finite (SignPattern s) := by infer_instance
  let _ : Nonempty (SignPattern s) := ⟨fun _ ↦ false⟩
  have hx :
      x ∈ interior
        (dom
          (pointwiseSupremumOn
            (Set.univ : Set (SignPattern s))
            (fun y σ ↦ (signedSlice s a σ y : WithTop ℝ)))) := by
    -- The sign-pattern supremum is the everywhere-finite absolute-value sum.
    rw [sum_abs_inner_eq_pointwiseSupremumOn_sign_patterns]
    have hdom :
        dom (fun y : V ↦ ∑ i ∈ s, (↑|⟪a i, y⟫| : WithTop ℝ)) = (Set.univ : Set V) := by
      ext y
      simp
    simp [hdom]
  have hmain :=
    subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials
      (ι := SignPattern s)
      (φ := fun y σ ↦ (signedSlice s a σ y : WithTop ℝ))
      (fun σ ↦ signed_slice_closedConvexFunction s a σ) hx
  have hactiveSet :
      {g | ∃ σ : SignPattern s,
          σ ∈ activePointwiseSupremumOnIndices
                (Set.univ : Set (SignPattern s))
                (fun y τ ↦ (signedSlice s a τ y : WithTop ℝ))
                x ∧
            g ∈ ∂ (fun y ↦ (signedSlice s a σ y : WithTop ℝ))(x)} =
        {g | ∃ σ : SignPattern s,
            σ ∈ activePointwiseSupremumOnIndices
                  (Set.univ : Set (SignPattern s))
                  (fun y τ ↦ (signedSlice s a τ y : WithTop ℝ))
                  x ∧
              g = signedVectorSum s a σ} := by
    ext g
    constructor
    · rintro ⟨σ, hσ, hg⟩
      rw [subdifferential_signed_inner_slice_eq_singleton] at hg
      exact ⟨σ, hσ, Set.mem_singleton_iff.mp hg⟩
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨σ, hσ, ?_⟩
      rw [subdifferential_signed_inner_slice_eq_singleton]
      simp
  -- Replace the finite supremum by the absolute-value sum, then compute the active hull.
  rw [← sum_abs_inner_eq_pointwiseSupremumOn_sign_patterns (s := s) (a := a)]
  rw [hmain, hactiveSet, active_signed_sums_eq_base_add_zero_pairs, convexHull_add,
    convexHull_singleton, convexHull_sum]
  simp [convexHull_pair]

end
