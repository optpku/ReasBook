/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part7

section Chap04
section Section21

/-- Helper for Theorem 21.4: if an affine function stays nonpositive along one whole ray,
then its linear part has nonpositive slope along that ray direction. -/
lemma helperForTheorem_21_4_affine_nonpositiveRay_forces_nonpositiveSlope
    {n : ℕ}
    (a : AffineMap ℝ (Fin n → ℝ) ℝ)
    (x0 d : Fin n → ℝ)
    (hRay :
      ∀ t : ℝ, 0 ≤ t → ((a (x0 + t • d) : ℝ) : EReal) ≤ (0 : EReal)) :
    a.linear d ≤ 0 := by
  by_contra hSlopePos
  have hSlopePos' : 0 < a.linear d := lt_of_not_ge hSlopePos
  let t : ℝ := (|a x0| + 1) / a.linear d
  have ht : 0 ≤ t := by
    -- The comparison point on the ray uses a nonnegative parameter.
    have hnum : 0 ≤ |a x0| + 1 := by positivity
    exact div_nonneg hnum hSlopePos'.le
  have hExpand :=
    (helperForTheorem_21_4_affineMonotone_and_constant_characterization a d).1
  have hAtT : ((a (x0 + t • d) : ℝ) : EReal) ≤ (0 : EReal) := hRay t ht
  rw [hExpand x0 t ht] at hAtT
  have hAtTReal : a x0 + t * a.linear d ≤ 0 := EReal.coe_le_coe_iff.mp hAtT
  have hSlopeNe : a.linear d ≠ 0 := ne_of_gt hSlopePos'
  have htMul : t * a.linear d = |a x0| + 1 := by
    -- Cancel the positive denominator in the chosen parameter.
    unfold t
    field_simp [hSlopeNe]
  have hPositiveRayValue : 0 < a x0 + t * a.linear d := by
    have hLower : -|a x0| ≤ a x0 := neg_abs_le (a x0)
    rw [htMul]
    linarith
  linarith

/-- Helper for Theorem 21.4: if every affine constraint in the finite block stays nonpositive
along a ray from one feasible point, then every constraint in that block is globally
nonincreasing along the ray direction. -/
lemma helperForTheorem_21_4_affineBlock_rayNonpositive_to_globalMonotonicity
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (x0 d : Fin n → ℝ)
    (hRay :
      ∀ i : I, i ∈ I0 →
        ∀ t : ℝ, 0 ≤ t → f i (x0 + t • d) ≤ (0 : EReal)) :
    ∀ i : I, i ∈ I0 →
      ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x := by
  intro i hi x t ht
  rcases hAffine i hi with ⟨a, ha⟩
  have hSlope : a.linear d ≤ 0 := by
    -- First read the sign of the slope from one feasible ray.
    apply helperForTheorem_21_4_affine_nonpositiveRay_forces_nonpositiveSlope a x0 d
    intro s hs
    simpa [ha] using hRay i hi s hs
  have hExpand :=
    (helperForTheorem_21_4_affineMonotone_and_constant_characterization a d).1
  rw [ha (x + t • d), ha x, hExpand x t ht]
  -- Then the affine expansion and the slope sign give the desired monotonicity.
  have hReal : a x + t * a.linear d ≤ a x := by
    nlinarith [hSlope, ht]
  exact_mod_cast hReal

/-- Helper for Theorem 21.4: once the affine block is globally monotone along a direction,
the weaker recession hypothesis upgrades monotonicity on the remaining indices to constancy. -/
lemma helperForTheorem_21_4_outsideMonotone_becomes_constant_of_affineBlockControl
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hConstOutside :
      ∀ d : Fin n → ℝ,
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
          ∀ i : I, i ∉ I0 →
            ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x)
    (x0 d : Fin n → ℝ)
    (hRay :
      ∀ i : I, i ∈ I0 →
        ∀ t : ℝ, 0 ≤ t → f i (x0 + t • d) ≤ (0 : EReal))
    (hOutsideMono :
      ∀ i : I, i ∉ I0 →
        ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) :
    ∀ i : I, i ∉ I0 →
      ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x := by
  have hMonoAll :
      ∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x := by
    intro i x t ht
    by_cases hi : i ∈ I0
    · exact
        helperForTheorem_21_4_affineBlock_rayNonpositive_to_globalMonotonicity
          f I0 hAffine x0 d hRay i hi x t ht
    · exact hOutsideMono i hi x t ht
  -- Route correction: the weaker hypothesis only acts after the affine block has been
  -- converted into global monotonicity, so we package that step separately here.
  exact hConstOutside d hMonoAll

/-- Helper for Theorem 21.4: the feasible set cut out by the finite affine block is a finite
intersection of nonpositive sublevel sets, hence it is closed and convex. -/
lemma helperForTheorem_21_4_affineFeasibleSet_closed_convex
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)}) :
    IsClosed {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} ∧
      Convex ℝ {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} := by
  let C : I → Set (Fin n → ℝ) := fun i => {x : Fin n → ℝ | f i x ≤ (0 : EReal)}
  have hClosedC : ∀ i : I, IsClosed (C i) := by
    intro i
    -- Each individual nonpositive sublevel is closed by the 21.3 sublevel helper.
    exact (helperForTheorem_21_3_nonpositiveSublevel_closed_convex
      (f := f i) (hfProper := hfProper i) (hfClosed := hfClosed i)).1
  have hConvC : ∀ i : I, Convex ℝ (C i) := by
    intro i
    -- The same helper also provides convexity of each sublevel set.
    exact (helperForTheorem_21_3_nonpositiveSublevel_closed_convex
      (f := f i) (hfProper := hfProper i) (hfClosed := hfClosed i)).2
  have hSetEq :
      {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} =
        {x : Fin n → ℝ | ∀ i ∈ I0, x ∈ C i} := by
    -- Rewrite the affine-feasible block as an ordinary finite intersection.
    ext x
    simp [C]
  constructor
  · -- Closedness comes from finite intersection of closed sets.
    simpa [hSetEq] using helperForText_21_3_3_isClosed_finiteIntersection C hClosedC I0
  · -- Convexity comes from finite intersection of convex sets.
    simpa [hSetEq] using helperForText_21_3_3_convex_finiteIntersection C hConvC I0

/-- Helper for Theorem 21.4: once a recession direction preserves the affine-feasible set,
monotonicity on the outside block upgrades to constancy there. -/
lemma helperForTheorem_21_4_affineFeasibleRecession_outsideMonotone_becomes_constant
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hConstOutside :
      ∀ d : Fin n → ℝ,
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
          ∀ i : I, i ∉ I0 →
            ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x)
    (hAne : ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)).Nonempty)
    {d : Fin n → ℝ}
    (hdA : d ∈ Set.recessionCone {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)})
    (hOutsideMono :
      ∀ i : I, i ∉ I0 →
        ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) :
    ∀ i : I, i ∉ I0 →
      ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x := by
  rcases hAne with ⟨x0, hx0⟩
  have hRay :
      ∀ i : I, i ∈ I0 →
        ∀ t : ℝ, 0 ≤ t → f i (x0 + t • d) ≤ (0 : EReal) := by
    intro i hi t ht
    -- Recession of the affine-feasible set keeps the chosen feasible point on the ray.
    exact hdA hx0 ht i hi
  -- Feed the ray control on the affine block into the previously isolated constancy step.
  exact helperForTheorem_21_4_outsideMonotone_becomes_constant_of_affineBlockControl
    f I0 hAffine hConstOutside x0 d hRay hOutsideMono

/-- Helper for Theorem 21.4: after isolating the affine-feasible block, failure of the global
primal system means there is no point of that block satisfying every remaining inequality. -/
lemma helperForTheorem_21_4_notPrimal_on_affineFeasibleSet
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal)) :
    ¬ ∃ x : Fin n → ℝ,
        (∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)) ∧
          ∀ i : I, i ∉ I0 → f i x ≤ (0 : EReal) := by
  intro hSplitPrimal
  rcases hSplitPrimal with ⟨x, hxAffine, hxOutside⟩
  apply hNotPrimal
  refine ⟨x, ?_⟩
  intro i
  by_cases hi : i ∈ I0
  · -- On the affine block we use the stored affine-feasibility part.
    exact hxAffine i hi
  · -- Outside the affine block we use the remaining inequalities directly.
    exact hxOutside i hi

/-- Helper for Theorem 21.4: after passing to the outside subtype `J = {i // i ∉ I₀}`,
the split nonprimal statement on the affine-feasible set is exactly the subtype-indexed
nonprimal statement one needs for the shifted finite-family route. -/
lemma helperForTheorem_21_4_notPrimal_on_affineFeasibleSet_outsideSubtype
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hNotPrimalOnA :
      ¬ ∃ x : Fin n → ℝ,
          (∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)) ∧
            ∀ i : I, i ∉ I0 → f i x ≤ (0 : EReal)) :
    ¬ ∃ x : Fin n → ℝ,
        x ∈ {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} ∧
          ∀ j : {i : I // i ∉ I0}, f j.1 x ≤ (0 : EReal) := by
  intro hSubtypePrimal
  rcases hSubtypePrimal with ⟨x, hxA, hxOutside⟩
  apply hNotPrimalOnA
  refine ⟨x, ?_, ?_⟩
  · -- The affine-feasible-set membership is exactly the first conjunct we need.
    simpa using hxA
  · -- Reinterpret the subtype-indexed inequalities as ordinary outside-index inequalities.
    intro i hi
    exact hxOutside ⟨i, hi⟩

/-- Helper for Theorem 21.4: a sparse global finite witness supported on the outside subtype
`{i // i ∉ I₀}` can be pushed forward along `Subtype.val` and then packaged into the same
support-bounded `Finsupp` format used elsewhere in Section 21.3. -/
lemma helperForTheorem_21_4_outsideSubtype_sparseDual_margin_to_supportBoundedFinsupp_margin
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hfinite :
      ∃ m : ℕ, m ≤ n + 1 ∧
        ∃ idx : Fin m → {i : I // i ∉ I0}, ∃ w : Fin m → ℝ,
          (∀ j : Fin m, 0 ≤ w j) ∧
            ∃ ε : ℝ, 0 < ε ∧
              ∀ x : Fin n → ℝ,
                ((ε : ℝ) : EReal) ≤
                  ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 x) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ,
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  -- Reindex the outside-subtype witness back to `I` without changing the inequality.
  apply helperForTheorem_21_3_noninjectiveSparseDual_margin_on_univ_to_supportBoundedFinsupp_margin
    (f := f)
  rcases hfinite with ⟨m, hm, idx, w, hwNonneg, ε, hε, hmargin⟩
  refine ⟨m, hm, (fun j => (idx j).1), w, hwNonneg, ε, hε, ?_⟩
  intro x
  simpa using hmargin x

/-- Helper for Theorem 21.4: likewise, a sparse global finite witness supported on the affine
block subtype `{i // i ∈ I₀}` can be pushed forward to the ambient index type and packaged as
the standard support-bounded `Finsupp` certificate. -/
lemma helperForTheorem_21_4_affineBlockSubtype_sparseDual_margin_to_supportBoundedFinsupp_margin
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hfinite :
      ∃ m : ℕ, m ≤ n + 1 ∧
        ∃ idx : Fin m → {i : I // i ∈ I0}, ∃ w : Fin m → ℝ,
          (∀ j : Fin m, 0 ≤ w j) ∧
            ∃ ε : ℝ, 0 < ε ∧
              ∀ x : Fin n → ℝ,
                ((ε : ℝ) : EReal) ≤
                  ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 x) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ,
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  -- This is the same pushforward step, now from the affine-block subtype.
  apply helperForTheorem_21_3_noninjectiveSparseDual_margin_on_univ_to_supportBoundedFinsupp_margin
    (f := f)
  rcases hfinite with ⟨m, hm, idx, w, hwNonneg, ε, hε, hmargin⟩
  refine ⟨m, hm, (fun j => (idx j).1), w, hwNonneg, ε, hε, ?_⟩
  intro x
  simpa using hmargin x

/-- Helper for Theorem 21.4: once every active outside-subtype term is constant along a ray,
their weighted `EReal` sum is constant along the same ray. -/
lemma helperForTheorem_21_4_outsideSubtype_weightedSum_const_of_coordinatewiseConst
    {n m : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (idx : Fin m → {i : I // i ∉ I0})
    (w : Fin m → ℝ)
    {x d : Fin n → ℝ}
    (hConst :
      ∀ j : Fin m, ∀ t : ℝ, 0 ≤ t →
        f (idx j).1 (x + t • d) = f (idx j).1 x) :
    ∀ t : ℝ, 0 ≤ t →
      ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 (x + t • d) =
        ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 x := by
  intro t ht
  -- Rewrite each summand using the coordinatewise constancy hypothesis.
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [hConst j t ht]

/-- Helper for Theorem 21.4: along a recession direction of the affine-feasible block, any
weighted outside-subtype sum is constant as soon as each outside term is monotone there. -/
lemma helperForTheorem_21_4_outsideSubtype_weightedSum_recessionInvariant_of_outsideMonotonicity
    {n m : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hConstOutside :
      ∀ d : Fin n → ℝ,
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
          ∀ i : I, i ∉ I0 →
            ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x)
    (hAne : ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)).Nonempty)
    (idx : Fin m → {i : I // i ∉ I0})
    (w : Fin m → ℝ)
    {d : Fin n → ℝ}
    (hdA : d ∈ Set.recessionCone {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)})
    (hOutsideMono :
      ∀ i : I, i ∉ I0 →
        ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) :
    ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
      ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 (x + t • d) =
        ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 x := by
  intro x t ht
  -- First upgrade outside monotonicity to coordinatewise constancy along the recession ray.
  have hCoordConst :
      ∀ j : Fin m, ∀ s : ℝ, 0 ≤ s →
        f (idx j).1 (x + s • d) = f (idx j).1 x := by
    intro j s hs
    exact
      helperForTheorem_21_4_affineFeasibleRecession_outsideMonotone_becomes_constant
        f I0 hAffine hConstOutside hAne hdA hOutsideMono (idx j).1 (idx j).2 x s hs
  -- Then sum the coordinatewise equalities termwise.
  simpa using
    helperForTheorem_21_4_outsideSubtype_weightedSum_const_of_coordinatewiseConst
      f I0 idx w hCoordConst t ht

/-- Helper for Theorem 21.4: if the affine-feasible set is nonempty but the outside-subtype
primal system already fails there, then the outside subtype itself cannot be empty. -/
lemma helperForTheorem_21_4_outsideSubtype_nonempty_of_notPrimalOnAffineFeasibleSet
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hA : ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)).Nonempty)
    (hNotPrimalOnOutsideSubtype :
      ¬ ∃ x : Fin n → ℝ,
          x ∈ {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} ∧
            ∀ j : {i : I // i ∉ I0}, f j.1 x ≤ (0 : EReal)) :
    ¬ IsEmpty {i : I // i ∉ I0} := by
  intro hJempty
  rcases hA with ⟨x, hxA⟩
  -- If the outside subtype were empty, any `x ∈ A` would satisfy the outside block vacuously.
  apply hNotPrimalOnOutsideSubtype
  refine ⟨x, hxA, ?_⟩
  intro j
  let _ : IsEmpty {i : I // i ∉ I0} := hJempty
  exact isEmptyElim j

/-- Helper for Theorem 21.4: once the outside-subtype system on the affine-feasible set has
the full `Theorem 21.3` no-common-recession hypothesis, the standard sparse-margin machinery
already yields an `A`-local certificate. -/
lemma helperForTheorem_21_4_affineFeasibleSet_local_sparseMargin_of_noCommonRecession
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hA : ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)).Nonempty)
    (hAclosed : IsClosed {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)})
    (hAconv : Convex ℝ {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)})
    (hNoCommonRecessionOnA :
      ¬ ∃ d : Fin n → ℝ,
          d ≠ 0 ∧
            d ∈ Set.recessionCone {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} ∧
              (∀ j : {i : I // i ∉ I0},
                ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f j.1 (x + t • d) ≤ f j.1 x))
    (hNotPrimalOnOutsideSubtype :
      ¬ ∃ x : Fin n → ℝ,
          x ∈ {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} ∧
            ∀ j : {i : I // i ∉ I0}, f j.1 x ≤ (0 : EReal)) :
    ∃ m : ℕ, m ≤ n + 1 ∧
      ∃ idx : Fin m → {i : I // i ∉ I0}, ∃ w : Fin m → ℝ,
        (∀ j : Fin m, 0 ≤ w j) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ,
              x ∈ {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} →
                ((ε : ℝ) : EReal) ≤
                  ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 x := by
  have hJnonempty : ¬ IsEmpty {i : I // i ∉ I0} :=
    helperForTheorem_21_4_outsideSubtype_nonempty_of_notPrimalOnAffineFeasibleSet
      f I0 hA hNotPrimalOnOutsideSubtype
  -- Under the stronger no-common-recession hypothesis on `A`, this is exactly the
  -- previously proved `Theorem 21.3` extraction pipeline for the outside subtype.
  rcases helperForTheorem_21_3_notPrimal_to_finiteDual_margin
      ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)})
      hA hAclosed hAconv
      (fun j : {i : I // i ∉ I0} => f j.1)
      (fun j : {i : I // i ∉ I0} => hfProper j.1)
      (fun j : {i : I // i ∉ I0} => hfClosed j.1)
      hNoCommonRecessionOnA
      hJnonempty
      hNotPrimalOnOutsideSubtype with
    ⟨m, hm, idx, -, w, hwNonneg, ε, hε, hmargin⟩
  -- Forget the injectivity data: the current endpoint only needs a sparse local witness.
  exact ⟨m, hm, idx, w, hwNonneg, ε, hε, hmargin⟩

/-- Helper for Theorem 21.4: once one affine slice of a closed convex set is bounded,
every nonempty parallel slice has trivial recession cone. This is the Chapter 2
parallel-slice boundedness transfer, packaged here for the bounded-slice route on the
affine-feasible set. -/
lemma helperForTheorem_21_4_parallelAffineSlice_recessionCone_eq_singleton_zero
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    {M M' : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))}
    (hMCne : ((M : Set (EuclideanSpace ℝ (Fin n))) ∩ C).Nonempty)
    (hMCbdd : Bornology.IsBounded ((M : Set (EuclideanSpace ℝ (Fin n))) ∩ C))
    (hM'Cne : ((M' : Set (EuclideanSpace ℝ (Fin n))) ∩ C).Nonempty)
    (hparallel : M'.direction = M.direction) :
    Set.recessionCone ((M' : Set (EuclideanSpace ℝ (Fin n))) ∩ C) =
      ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
  -- Reuse the closed-convex parallel-slice transfer from Chapter 2 verbatim.
  exact
    boundedness_via_recessionCone_inter (C := C) hCclosed hCconv
      (M := M) (M' := M') hMCne hMCbdd hM'Cne hparallel

/-- Helper for Theorem 21.4: the same bounded affine slice controls every parallel slice,
so after choosing one transverse bounded section of the affine-feasible set, all translated
sections with the same direction are bounded as well. -/
lemma helperForTheorem_21_4_parallelAffineSlice_bounded
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (M : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
    (hMCne : ((M : Set (EuclideanSpace ℝ (Fin n))) ∩ C).Nonempty)
    (hMCbdd : Bornology.IsBounded ((M : Set (EuclideanSpace ℝ (Fin n))) ∩ C)) :
    ∀ (M' : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))),
      M'.direction = M.direction →
        Bornology.IsBounded ((M' : Set (EuclideanSpace ℝ (Fin n))) ∩ C) := by
  intro M' hparallel
  -- Once one transverse slice is bounded, Chapter 2 propagates boundedness to all parallels.
  exact
    bounded_inter_of_parallel_affine (C := C) hCclosed hCconv M hMCne hMCbdd M' hparallel

/-- Helper for Theorem 21.4: the epigraph of a real affine map, viewed as an `EReal`-valued
function, is closed. -/
lemma helperForTheorem_21_4_affine_ereal_epigraph_closed
    {n : ℕ}
    (a : AffineMap ℝ (Fin n → ℝ) ℝ) :
    IsClosed {p : (Fin n → ℝ) × ℝ | (((a p.1 : ℝ) : EReal)) ≤ (p.2 : EReal)} := by
  -- Rewrite the `EReal` comparison back to an ordinary real inequality.
  have hEq :
      {p : (Fin n → ℝ) × ℝ | (((a p.1 : ℝ) : EReal)) ≤ (p.2 : EReal)} =
        {p : (Fin n → ℝ) × ℝ | a p.1 ≤ p.2} := by
    ext p
    simp
  -- The real-valued epigraph of a continuous affine map is closed.
  rw [hEq]
  exact isClosed_le ((AffineMap.continuous_of_finiteDimensional a).comp continuous_fst) continuous_snd

/-- Helper for Theorem 21.4: an affine map on `ℝⁿ` that is nonnegative everywhere has zero
linear part, hence is constant. -/
lemma helperForTheorem_21_4_affine_nonnegative_on_univ_is_constant
    {n : ℕ}
    (a : AffineMap ℝ (Fin n → ℝ) ℝ)
    (hNonneg : ∀ x : Fin n → ℝ, 0 ≤ a x) :
    ∀ x : Fin n → ℝ, a x = a 0 := by
  have hLinearZero : ∀ d : Fin n → ℝ, a.linear d = 0 := by
    intro d
    have hRayForward :
        ∀ t : ℝ, 0 ≤ t → ((((-a) (0 + t • d) : ℝ) : EReal)) ≤ (0 : EReal) := by
      intro t ht
      have hreal : (-a) (0 + t • d) ≤ 0 := by
        simpa using (neg_nonpos.mpr (hNonneg (0 + t • d)))
      exact_mod_cast hreal
    have hRayBackward :
        ∀ t : ℝ, 0 ≤ t → ((((-a) (0 + t • (-d)) : ℝ) : EReal)) ≤ (0 : EReal) := by
      intro t ht
      have hreal : (-a) (0 + t • (-d)) ≤ 0 := by
        simpa using (neg_nonpos.mpr (hNonneg (0 + t • (-d))))
      exact_mod_cast hreal
    have hSlopeForward : (-a).linear d ≤ 0 :=
      helperForTheorem_21_4_affine_nonpositiveRay_forces_nonpositiveSlope (-a) 0 d hRayForward
    have hSlopeBackward : (-a).linear (-d) ≤ 0 :=
      helperForTheorem_21_4_affine_nonpositiveRay_forces_nonpositiveSlope (-a) 0 (-d) hRayBackward
    have hge : 0 ≤ a.linear d := by
      have : -(a.linear d) ≤ 0 := by simpa using hSlopeForward
      linarith
    have hle : a.linear d ≤ 0 := by
      simpa using hSlopeBackward
    exact le_antisymm hle hge
  intro x
  -- Vanishing linear part forces translation-invariance in the direction `x`.
  have hxConstE : ((a (0 + (1 : ℝ) • x) : ℝ) : EReal) = (a 0 : EReal) :=
    (helperForTheorem_21_4_affineMonotone_and_constant_characterization a x).2.2
      (hLinearZero x) 0 1 (by norm_num)
  exact EReal.coe_eq_coe_iff.mp (by simpa using hxConstE)

/-- Helper for Theorem 21.4: if the affine-feasible block is empty, Helly already extracts a
subfamily of at most `n + 1` affine constraints with empty common nonpositive sublevel set. -/
lemma helperForTheorem_21_4_emptyAffineFeasibleSet_has_small_infeasible_affineBlock
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hAempty :
      ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)) = ∅) :
    ∃ m : ℕ, m ≤ n + 1 ∧
      ∃ idx : Fin m → {i : I // i ∈ I0}, Function.Injective idx ∧
        ¬ ∃ x : Fin n → ℝ, ∀ j : Fin m, f (idx j).1 x ≤ (0 : EReal) := by
  classical
  let p : ℕ := Fintype.card {i : I // i ∈ I0}
  let e : {i : I // i ∈ I0} ≃ Fin p := Fintype.equivFin {i : I // i ∈ I0}
  let g : Fin p → (Fin n → ℝ) → EReal := fun j x => f (e.symm j).1 x
  have hgProper :
      ∀ j : Fin p, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g j) := by
    intro j
    -- Each affine member of the finite block is proper convex when viewed as an `EReal` map.
    rcases hAffine (e.symm j).1 (e.symm j).2 with ⟨a, ha⟩
    simpa [g, ha] using helperForTheorem_21_2_shifted_affine_properConvex (n := n) a 0
  have hgClosed :
      ∀ j : Fin p, IsClosed {q : (Fin n → ℝ) × ℝ | g j q.1 ≤ (q.2 : EReal)} := by
    intro j
    -- Closedness is inherited from the affine real epigraph model.
    rcases hAffine (e.symm j).1 (e.symm j).2 with ⟨a, ha⟩
    simpa [g, ha] using helperForTheorem_21_4_affine_ereal_epigraph_closed (n := n) a
  have hZeroGap :
      ¬ (⋂ j : Fin p,
          (Set.univ : Set (Fin n → ℝ)) ∩ {x : Fin n → ℝ | g j x ≤ (0 : EReal)}).Nonempty := by
    intro hNonempty
    rcases hNonempty with ⟨x, hx⟩
    have hxAffine :
        x ∈ {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} := by
      -- Route correction: rewrite the global affine-feasible set through the finite reindexing.
      simp only [Set.mem_setOf_eq]
      intro i hi
      have hxj :
          x ∈ (Set.univ : Set (Fin n → ℝ)) ∩ {x : Fin n → ℝ | g (e ⟨i, hi⟩) x ≤ (0 : EReal)} :=
        Set.mem_iInter.mp hx (e ⟨i, hi⟩)
      simpa [g] using hxj.2
    have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
      simpa [hAempty] using hxAffine
    simpa using hxEmpty
  rcases
      helperForTheorem_21_3_exists_small_zero_infeasible_subfamily_fin
        (C := (Set.univ : Set (Fin n → ℝ)))
        (hCclosed := isClosed_univ)
        (hCconvex := convex_univ)
        (g := g) hgProper hgClosed hZeroGap with
    ⟨m, hm, idx, hidx, hSmallGap⟩
  refine ⟨m, hm, fun j => e.symm (idx j), ?_, ?_⟩
  · -- Injectivity survives after transporting the chosen `Fin`-subfamily back to the subtype.
    intro j1 j2 hEq
    apply hidx
    exact e.symm.injective hEq
  · intro hFeasible
    apply hSmallGap
    rcases hFeasible with ⟨x, hx⟩
    refine ⟨x, Set.mem_iInter.mpr ?_⟩
    intro j
    refine ⟨trivial, ?_⟩
    simpa [g] using hx j

/-- Helper for Theorem 21.4: when the affine-feasible block is empty, a Helly-small affine
subfamily already admits a nonnegative weighted sum with a uniform positive lower bound. -/
lemma helperForTheorem_21_4_positive_margin_of_small_infeasible_affineBlock
    {n m : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (idx : Fin m → {i : I // i ∈ I0})
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hSmallGap :
      ¬ ∃ x : Fin n → ℝ, ∀ j : Fin m, f (idx j).1 x ≤ (0 : EReal)) :
    ∃ w : Fin m → ℝ,
      (∀ j : Fin m, 0 ≤ w j) ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ x : Fin n → ℝ,
            ε ≤ ∑ j : Fin m, w j * (Classical.choose (hAffine (idx j).1 (idx j).2) x) := by
  classical
  let a : Fin m → AffineMap ℝ (Fin n → ℝ) ℝ :=
    fun j => Classical.choose (hAffine (idx j).1 (idx j).2)
  have ha_eval :
      ∀ j : Fin m, ∀ x : Fin n → ℝ, f (idx j).1 x = (a j x : EReal) := by
    intro j x
    exact Classical.choose_spec (hAffine (idx j).1 (idx j).2) x
  let Φ : (Fin n → ℝ) →ᵃ[ℝ] (Fin m → ℝ) :=
    { toFun := fun x j => a j x
      linear := LinearMap.pi fun j => (a j).linear
      map_vadd' := by
        intro x d
        ext j
        simpa using (a j).map_vadd x d }
  let U : Set (Fin m → ℝ) := Φ '' (Set.univ : Set (Fin n → ℝ))
  let N : Set (Fin m → ℝ) := {u : Fin m → ℝ | ∀ j : Fin m, u j ≤ 0}
  -- The affine image is nonempty and convex, while the orthant is polyhedral convex.
  have hUne : U.Nonempty := by
    refine ⟨Φ 0, ?_⟩
    exact ⟨0, trivial, rfl⟩
  have hUconv : Convex ℝ U := by
    simpa [U] using (convex_univ.affine_image Φ)
  have hNdata : N.Nonempty ∧ Convex ℝ N := by
    simpa [N] using helperForTheorem_21_2_nonpositiveOrthant_nonempty_convex m
  have hNpoly : IsPolyhedralConvexSet m N := by
    simpa [N] using helperForTheorem_21_2_nonpositiveOrthant_polyhedral m
  have hUNdisj : Disjoint U N := by
    refine Set.disjoint_left.2 ?_
    intro u huU huN
    rcases huU with ⟨x, -, rfl⟩
    apply hSmallGap
    refine ⟨x, ?_⟩
    intro j
    have huj : a j x ≤ 0 := huN j
    have hujE : ((a j x : ℝ) : EReal) ≤ (0 : EReal) := by
      exact_mod_cast huj
    simpa [a] using (ha_eval j x).symm ▸ hujE
  have hNriUempty : N ∩ intrinsicInterior ℝ U = (∅ : Set (Fin m → ℝ)) := by
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    intro u hu
    rcases hu with ⟨huN, huRiU⟩
    exact (Set.disjoint_left.mp hUNdisj) (intrinsicInterior_subset huRiU) huN
  rcases
      (exists_hyperplaneSeparatesProperly_and_not_subset_right_iff_inter_intrinsicInterior_eq_empty_of_nonempty_convex_polyhedral_left
        m N U hNdata.1 hUne hUconv hNpoly).2 hNriUempty with
    ⟨H, hHproperNU, hUnotSubsetH⟩
  have hHproperUN : HyperplaneSeparatesProperly m H U N :=
    hyperplaneSeparatesProperly_comm hHproperNU
  rcases hyperplaneSeparatesProperly_oriented m H U N hHproperUN with
    ⟨b, β, hb_ne_zero, hHdef, hU_lower, hN_upper, _hNotBoth⟩
  let O : Set (Fin m → ℝ) := {u : Fin m → ℝ | ∀ j : Fin m, u j < 0}
  have hO_upper : ∀ u ∈ O, u ⬝ᵥ b ≤ β := by
    intro u huO
    exact hN_upper u (by
      intro j
      exact (huO j).le)
  have hb_nonneg : ∀ j : Fin m, 0 ≤ b j :=
    helperForTheorem_21_1_separatorNormal_nonneg_on_negativeOrthant O rfl b β hO_upper
  have hβ_nonneg : 0 ≤ β :=
    helperForTheorem_21_1_separatorBeta_nonneg_on_negativeOrthant O rfl b β hO_upper hb_ne_zero
      hb_nonneg
  let fAffine : Fin m → (Fin n → ℝ) → ℝ := fun j x => a j x
  have hAffineBlock : ∀ j : Fin m, ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g := by
    intro j
    exact ⟨a j, rfl⟩
  rcases helperForTheorem_21_2_supportWeightedAffine_properConvex_and_dom
      (C := (Set.univ : Set (Fin n → ℝ))) fAffine hAffineBlock b with
    ⟨gSupport, hgSupport_eval, _hgProper, _hDom⟩
  have hDotEq :
      ∀ x : Fin n → ℝ, (Φ x) ⬝ᵥ b = gSupport x := by
    intro x
    calc
      (Φ x) ⬝ᵥ b = ∑ j : Fin m, a j x * b j := by
        simp [Φ, dotProduct]
      _ = ∑ j : Fin m, b j * fAffine j x := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [fAffine, mul_comm]
      _ = gSupport x := by
        symm
        exact hgSupport_eval x
  have hSupportLower : ∀ x : Fin n → ℝ, β ≤ gSupport x := by
    intro x
    calc
      β ≤ (Φ x) ⬝ᵥ b := hU_lower (Φ x) ⟨x, by simp, rfl⟩
      _ = gSupport x := hDotEq x
  rcases Set.not_subset.mp hUnotSubsetH with ⟨u0, hu0U, hu0notH⟩
  rcases hu0U with ⟨x0, -, rfl⟩
  have hx0_ne : (Φ x0) ⬝ᵥ b ≠ β := by
    intro hx0eq
    apply hu0notH
    simpa [hHdef, hx0eq]
  have hx0_strict : β < gSupport x0 := by
    have hx0_ge : β ≤ (Φ x0) ⬝ᵥ b := hU_lower (Φ x0) ⟨x0, by simp, rfl⟩
    have hx0_gt' : β < (Φ x0) ⬝ᵥ b := lt_of_le_of_ne hx0_ge (Ne.symm hx0_ne)
    simpa [hDotEq x0] using hx0_gt'
  let gShift : (Fin n → ℝ) →ᵃ[ℝ] ℝ := gSupport - AffineMap.const ℝ (Fin n → ℝ) β
  have hShiftNonneg : ∀ x : Fin n → ℝ, 0 ≤ gShift x := by
    intro x
    have hxLower : β ≤ gSupport x := hSupportLower x
    simpa [gShift] using sub_nonneg.mpr hxLower
  have hShiftConst : ∀ x : Fin n → ℝ, gShift x = gShift 0 :=
    helperForTheorem_21_4_affine_nonnegative_on_univ_is_constant gShift hShiftNonneg
  have hx0ShiftPos : 0 < gShift x0 := by
    have : 0 < gSupport x0 - β := by
      linarith
    simpa [gShift] using this
  have hεpos : 0 < gShift 0 := by
    have hx0Eq : gShift x0 = gShift 0 := hShiftConst x0
    rw [hx0Eq] at hx0ShiftPos
    exact hx0ShiftPos
  refine ⟨b, hb_nonneg, gShift 0, hεpos, ?_⟩
  intro x
  have hxEq : gShift x = gShift 0 := hShiftConst x
  have hxLower : β ≤ gSupport x := hSupportLower x
  have hmarginReal : gShift 0 ≤ gSupport x := by
    have hxShiftEq : gSupport x - β = gShift 0 := by
      simpa [gShift] using hxEq
    linarith
  have hsumEq : gSupport x = ∑ j : Fin m, b j * Classical.choose (hAffine (idx j).1 (idx j).2) x := by
    calc
      gSupport x = ∑ j : Fin m, b j * fAffine j x := hgSupport_eval x
      _ = ∑ j : Fin m, b j * Classical.choose (hAffine (idx j).1 (idx j).2) x := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [fAffine, a]
  rw [← hsumEq]
  exact hmarginReal

/-- Helper for Theorem 21.4: the Fenchel conjugate of an affine real-valued map is the
indicator of a singleton, shifted by the affine constant. -/
lemma helperForTheorem_21_4_fenchelConjugate_affine_eq_indicator_singleton_add_const
    {n : ℕ}
    (a : AffineMap ℝ (Fin n → ℝ) ℝ) :
    ∃ b : Fin n → ℝ, ∃ β : ℝ,
      (∀ x : Fin n → ℝ, a x = x ⬝ᵥ b - β) ∧
      fenchelConjugate n (fun x : Fin n → ℝ => (a x : EReal)) =
        fun xStar : Fin n → ℝ =>
          indicatorFunction ({b} : Set (Fin n → ℝ)) xStar + (β : EReal) := by
  rcases affineMap_exists_dotProduct_sub (h := a) with ⟨b, β, hb⟩
  refine ⟨b, β, hb, ?_⟩
  funext xStar
  refine EReal.eq_of_forall_le_coe_iff ?_
  intro μ
  constructor
  · intro hμ
    by_cases hx : xStar = b
    · have hAff :
          ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ (a x : EReal) :=
        (fenchelConjugate_le_coe_iff_affine_le
          (n := n) (f := fun x : Fin n → ℝ => (a x : EReal)) (b := xStar) (μ := μ)).1 hμ
      have hβ_le : β ≤ μ := by
        have hAtZero := hAff 0
        have hAtZero' : ((-μ : ℝ) : EReal) ≤ ((-β : ℝ) : EReal) := by
          simpa [hx, hb 0] using hAtZero
        exact by
          have hreal : -μ ≤ -β := EReal.coe_le_coe_iff.mp hAtZero'
          linarith
      have hβE : (β : EReal) ≤ (μ : EReal) := by exact_mod_cast hβ_le
      simpa [hx, indicatorFunction, hβE]
    · have hFalse :
          ¬ fenchelConjugate n (fun x : Fin n → ℝ => (a x : EReal)) xStar ≤ (μ : EReal) := by
        intro hle
        have hAff :
            ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ (a x : EReal) :=
          (fenchelConjugate_le_coe_iff_affine_le
            (n := n) (f := fun x : Fin n → ℝ => (a x : EReal)) (b := xStar) (μ := μ)).1 hle
        let d : Fin n → ℝ := xStar - b
        have hd_ne : d ≠ 0 := by
          intro hd0
          apply hx
          have hsub : xStar - b = 0 := by simpa [d] using hd0
          exact sub_eq_zero.mp hsub
        have hdd_nonneg : 0 ≤ d ⬝ᵥ d := dotProduct_self_nonneg (v := d)
        have hdd_ne : d ⬝ᵥ d ≠ 0 := dotProduct_self_ne_zero d hd_ne
        have hdd_pos : 0 < d ⬝ᵥ d := lt_of_le_of_ne hdd_nonneg hdd_ne.symm
        let t : ℝ := (|μ - β| + 1) / (d ⬝ᵥ d)
        have ht_nonneg : 0 ≤ t := by
          refine div_nonneg ?_ hdd_pos.le
          positivity
        have hAtT := hAff (t • d)
        have hAtTReal :
            (t • d) ⬝ᵥ xStar - μ ≤ a (t • d) := by
          exact EReal.coe_le_coe_iff.mp hAtT
        have hxStar_decomp : xStar = d + b := by
          ext i
          simp [d, sub_eq_add_neg, add_assoc]
        have hcalc :
            a (t • d) = (t • d) ⬝ᵥ b - β := hb (t • d)
        have hineq : t * (d ⬝ᵥ d) ≤ μ - β := by
          rw [hcalc] at hAtTReal
          have hAtTReal' :
              t * (d ⬝ᵥ xStar) - μ ≤ t * (d ⬝ᵥ b) - β := by
            simpa [dotProduct_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hAtTReal
          have hxStar_dot : d ⬝ᵥ xStar = d ⬝ᵥ d + d ⬝ᵥ b := by
            calc
              d ⬝ᵥ xStar = d ⬝ᵥ (d + b) := by rw [hxStar_decomp]
              _ = d ⬝ᵥ d + d ⬝ᵥ b := by simp [dotProduct_add]
          rw [hxStar_dot] at hAtTReal'
          nlinarith
        have htd_eq : t * (d ⬝ᵥ d) = |μ - β| + 1 := by
          unfold t
          field_simp [hdd_pos.ne']
        have habs_ge : μ - β ≤ |μ - β| := le_abs_self (μ - β)
        rw [htd_eq] at hineq
        linarith
      exfalso
      exact hFalse hμ
  · intro hμ
    by_cases hx : xStar = b
    · have hβE : (β : EReal) ≤ (μ : EReal) := by
        simpa [hx, indicatorFunction] using hμ
      have hβ : β ≤ μ := EReal.coe_le_coe_iff.mp hβE
      refine (fenchelConjugate_le_coe_iff_affine_le
        (n := n) (f := fun x : Fin n → ℝ => (a x : EReal)) (b := xStar) (μ := μ)).2 ?_
      intro x
      have hreal : x ⬝ᵥ b - μ ≤ x ⬝ᵥ b - β := by
        linarith
      simpa [hx, hb x] using (show ((x ⬝ᵥ b - μ : ℝ) : EReal) ≤ ((x ⬝ᵥ b - β : ℝ) : EReal) from by
        exact_mod_cast hreal)
    · exfalso
      simpa [hx, indicatorFunction] using hμ

/-- Helper for Theorem 21.4: the effective domain of the conjugate of an affine map is the
singleton consisting of its linear part in dot-product coordinates. -/
lemma helperForTheorem_21_4_effectiveDomain_fenchelConjugate_affine_eq_singleton
    {n : ℕ}
    (a : AffineMap ℝ (Fin n → ℝ) ℝ) :
    ∃ b : Fin n → ℝ, ∃ β : ℝ,
      (∀ x : Fin n → ℝ, a x = x ⬝ᵥ b - β) ∧
      effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (fenchelConjugate n (fun x : Fin n → ℝ => (a x : EReal))) = ({b} : Set (Fin n → ℝ)) := by
  rcases helperForTheorem_21_4_fenchelConjugate_affine_eq_indicator_singleton_add_const a with
    ⟨b, β, hb, hconj⟩
  refine ⟨b, β, hb, ?_⟩
  ext xStar
  by_cases hx : xStar = b
  · simp [hconj, effectiveDomain_eq, indicatorFunction, hx]
  · have htop :
        indicatorFunction ({b} : Set (Fin n → ℝ)) xStar + (β : EReal) = (⊤ : EReal) := by
        simp [indicatorFunction, hx]
    simp [hconj, effectiveDomain_eq, hx, htop]

/-- Helper for Theorem 21.4: a nonzero point of the effective domain of the positively
homogeneous hull of a convex-hull family admits a finite witness whose support points already
lie in the effective domains of the original family members. -/
lemma helperForTheorem_21_4_nonzero_effectiveDomain_posHomHullFamily_has_domainWitness
    {n : ℕ} {ι : Type*}
    (g : ι → (Fin n → ℝ) → EReal)
    (hgProper : ∀ i : ι, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g i))
    {x : Fin n → ℝ}
    (hx_ne : x ≠ 0)
    (hxDom :
      x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (positivelyHomogeneousConvexFunctionGenerated (convexHullFunctionFamily g))) :
    ∃ m : ℕ, m ≤ n + 1 ∧
      ∃ idx : Fin m → ι, ∃ x' : Fin m → Fin n → ℝ, ∃ c : Fin m → ℝ,
        (∀ j : Fin m, 0 < c j) ∧
        x = ∑ j : Fin m, c j • x' j ∧
        AffineIndependent ℝ x' ∧
        ∀ j : Fin m, x' j ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (g (idx j)) := by
  classical
  let k : (Fin n → ℝ) → EReal :=
    positivelyHomogeneousConvexFunctionGenerated (convexHullFunctionFamily g)
  let S : Set EReal :=
    { z : EReal |
      ∃ m : Nat, m ≤ n + 1 ∧
        ∃ (idx : Fin m → ι) (x' : Fin m → Fin n → ℝ) (c : Fin m → ℝ),
          (∀ j, 0 < c j) ∧
            x = ∑ j, c j • x' j ∧
            AffineIndependent ℝ x' ∧
            z = ∑ j, ((c j : ℝ) : EReal) * g (idx j) (x' j) }
  have hk_repr :
      k x = sInf S := by
    simpa [k, S] using
      positivelyHomogeneousConvexFunctionGenerated_convexHullFunctionFamily_eq_sInf_linearIndependent_nonnegLinearCombination_le
        (fᵢ := g) hgProper x hx_ne
  have hk_ne_top : k x ≠ (⊤ : EReal) := by
    have hxlt : k x < (⊤ : EReal) := by
      simpa [k, effectiveDomain_eq] using hxDom
    exact (lt_top_iff_ne_top).1 hxlt
  have hWitnessFinite :
      ∃ z ∈ S, z ≠ (⊤ : EReal) := by
    by_contra hNoFinite
    push_neg at hNoFinite
    have hsInf_top : sInf S = (⊤ : EReal) := by
      apply le_antisymm le_top
      exact le_sInf (by
        intro z hz
        simpa [hNoFinite z hz])
    exact hk_ne_top (hk_repr.trans hsInf_top)
  rcases hWitnessFinite with ⟨z, hzS, hz_ne_top⟩
  rcases hzS with ⟨m, hm, idx, x', c, hcpos, hxsum, hAffInd, hzEq⟩
  refine ⟨m, hm, idx, x', c, hcpos, hxsum, hAffInd, ?_⟩
  intro j
  have hterm_ne_top :
      ((c j : ℝ) : EReal) * g (idx j) (x' j) ≠ (⊤ : EReal) := by
    intro htop
    have hterm_ne_bot :
        ∀ k' : Fin m, ((c k' : ℝ) : EReal) * g (idx k') (x' k') ≠ (⊥ : EReal) := by
      intro k'
      have hnotbot : g (idx k') (x' k') ≠ (⊥ : EReal) := (hgProper (idx k')).2.2 _ (by simp)
      exact ereal_mul_ne_bot_of_pos (hcpos k') hnotbot
    have hsum_top :
        ∑ k' : Fin m, ((c k' : ℝ) : EReal) * g (idx k') (x' k') = (⊤ : EReal) := by
      exact
        sum_eq_top_of_term_top (s := (Finset.univ : Finset (Fin m)))
          (f := fun k' : Fin m => ((c k' : ℝ) : EReal) * g (idx k') (x' k'))
          (i := j) (by simp) htop (by
            intro k' hk'
            exact hterm_ne_bot k')
    exact hz_ne_top (by simpa [hzEq] using hsum_top)
  have hg_ne_top : g (idx j) (x' j) ≠ (⊤ : EReal) := by
    intro htop
    have hposE : (0 : EReal) < ((c j : ℝ) : EReal) := by
      exact_mod_cast hcpos j
    have : ((c j : ℝ) : EReal) * g (idx j) (x' j) = (⊤ : EReal) := by
      simpa [htop] using EReal.mul_top_of_pos (x := ((c j : ℝ) : EReal)) hposE
    exact hterm_ne_top this
  simpa [effectiveDomain_eq] using
    (show x' j ∈ {y : Fin n → ℝ | y ∈ Set.univ ∧ g (idx j) y < (⊤ : EReal)} from
      ⟨by simp, (lt_top_iff_ne_top).2 hg_ne_top⟩)

/-- Helper for Theorem 21.4: if every member-domain point has zero pairing with `y`, then the
same holds for every nonzero point in the effective domain of the generated positively
homogeneous hull. -/
lemma helperForTheorem_21_4_dotProduct_zero_on_nonzero_effectiveDomain_posHomHullFamily
    {n : ℕ} {ι : Type*}
    (g : ι → (Fin n → ℝ) → EReal)
    (hgProper : ∀ i : ι, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g i))
    (y : Fin n → ℝ)
    (hZero :
      ∀ i : ι, ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (g i),
        dotProduct xStar y = 0)
    {x : Fin n → ℝ}
    (hx_ne : x ≠ 0)
    (hxDom :
      x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (positivelyHomogeneousConvexFunctionGenerated (convexHullFunctionFamily g))) :
    dotProduct x y = 0 := by
  rcases helperForTheorem_21_4_nonzero_effectiveDomain_posHomHullFamily_has_domainWitness
      g hgProper hx_ne hxDom with
    ⟨m, hm, idx, x', c, hcpos, hxsum, hAffInd, hxDom'⟩
  let _ := hm
  let _ := hAffInd
  have hdot :
      dotProduct x y = ∑ j : Fin m, c j * dotProduct (x' j) y := by
    calc
      dotProduct x y = dotProduct (∑ j : Fin m, c j • x' j) y := by rw [hxsum]
      _ = ∑ j : Fin m, dotProduct (c j • x' j) y := by
            simpa using (sum_dotProduct (s := (Finset.univ : Finset (Fin m)))
              (u := fun j : Fin m => c j • x' j) (v := y))
      _ = ∑ j : Fin m, c j * dotProduct (x' j) y := by
            simp [dotProduct_smul, smul_eq_mul]
  have hzeroTerms : ∀ j : Fin m, dotProduct (x' j) y = 0 := by
    intro j
    exact hZero (idx j) (x' j) (hxDom' j)
  rw [hdot]
  have : ∑ j : Fin m, c j * dotProduct (x' j) y = ∑ j : Fin m, 0 := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [hzeroTerms j]
  simp [this]

/-- Helper for Theorem 21.4: if a closed proper convex function is constant along the ray
direction `d`, then every point of the effective domain of its conjugate is orthogonal to `d`. -/
lemma helperForTheorem_21_4_dotProduct_zero_on_effectiveDomain_fenchelConjugate_of_constancy
    {n : ℕ}
    (g : (Fin n → ℝ) → EReal)
    (hgProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hgClosed : IsClosed {p : (Fin n → ℝ) × ℝ | g p.1 ≤ (p.2 : EReal)})
    (d : Fin n → ℝ)
    (hConst :
      ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → g (x + t • d) = g x) :
    ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g),
      dotProduct xStar d = 0 := by
  have hClosedConv : ClosedConvexFunction g := by
    refine ⟨?_, helperForTheorem_21_3_lowerSemicontinuous_of_closedEpigraph (f := g) (hfClosed := hgClosed)⟩
    simpa [ConvexFunction] using hgProper.1
  have hRecFun :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g)) =
        recessionFunction g := by
    exact
      section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction
        (n := n) (f := g) hClosedConv hgProper
  have hRecCone :
      d ∈ recessionConeEReal (F := (Fin n → ℝ)) g := by
    refine (section14_mem_recessionConeEReal_iff (g := g) (y := d)).2 ?_
    intro x hx
    have hEq : g (x + d) = g x := by
      simpa using hConst x 1 (by norm_num)
    have hx_ne_top : g x ≠ (⊤ : EReal) := (lt_top_iff_ne_top.mp hx)
    have hx_ne_bot : g x ≠ (⊥ : EReal) := hgProper.2.2 x (by simp)
    lift g x to ℝ using ⟨hx_ne_top, hx_ne_bot⟩ with r hr
    have hzero : (((r : ℝ) : EReal) - ((r : ℝ) : EReal)) ≤ (0 : EReal) := by
      simp [EReal.coe_sub]
    simpa [hr, hEq] using hzero
  have hRecConeNeg :
      (-d) ∈ recessionConeEReal (F := (Fin n → ℝ)) g := by
    refine (section14_mem_recessionConeEReal_iff (g := g) (y := -d)).2 ?_
    intro x hx
    have hEq' : g x = g (x + -d) := by
      have := hConst (x + -d) 1 (by norm_num)
      simpa [add_assoc, add_left_comm, add_comm] using this
    have hEq : g (x + -d) = g x := hEq'.symm
    have hx_ne_top : g x ≠ (⊤ : EReal) := (lt_top_iff_ne_top.mp hx)
    have hx_ne_bot : g x ≠ (⊥ : EReal) := hgProper.2.2 x (by simp)
    lift g x to ℝ using ⟨hx_ne_top, hx_ne_bot⟩ with r hr
    have hzero : (((r : ℝ) : EReal) - ((r : ℝ) : EReal)) ≤ (0 : EReal) := by
      simp [EReal.coe_sub]
    simpa [hr, hEq] using hzero
  have hRecLe :
      recessionFunction g d ≤ (0 : EReal) := by
    have hRecELe : recessionFunctionEReal (F := (Fin n → ℝ)) g d ≤ (0 : EReal) := by
      simpa [recessionConeEReal] using hRecCone
    simpa [recessionFunctionEReal, recessionFunction, erealDom, effectiveDomain_eq] using hRecELe
  have hRecLeNeg :
      recessionFunction g (-d) ≤ (0 : EReal) := by
    have hRecELe :
        recessionFunctionEReal (F := (Fin n → ℝ)) g (-d) ≤ (0 : EReal) := by
      simpa [recessionConeEReal] using hRecConeNeg
    simpa [recessionFunctionEReal, recessionFunction, erealDom, effectiveDomain_eq] using hRecELe
  have hSuppLe :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g)) d ≤
        ((0 : ℝ) : EReal) := by
    simpa [hRecFun] using hRecLe
  have hSuppLeNeg :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g)) (-d) ≤
        ((0 : ℝ) : EReal) := by
    simpa [hRecFun] using hRecLeNeg
  intro xStar hxStar
  have hle :
      dotProduct xStar d ≤ 0 := by
    exact
      (section13_supportFunctionEReal_le_coe_iff
        (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g))
        (y := d) (μ := 0)).1 hSuppLe xStar hxStar
  have hge :
      0 ≤ dotProduct xStar d := by
    have hleNeg :
        dotProduct xStar (-d) ≤ 0 := by
      exact
        (section13_supportFunctionEReal_le_coe_iff
          (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g))
          (y := -d) (μ := 0)).1 hSuppLeNeg xStar hxStar
    simpa using neg_nonneg.mpr hleNeg
  exact le_antisymm hle hge

end Section21
end Chap04
