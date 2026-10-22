/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_42
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Remark_9_37

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace ERealFunction

/-- The negative-coordinate index set of the second argument in the finite-dimensional
`φ`-divergence. -/
noncomputable def coordinatePhiDivergenceNegativeIndices {N : ℕ} (y : Fin N → ℝ) :
    Finset (Fin N) :=
  Finset.univ.filter fun i ↦ y i < 0

/-- The zero-coordinate index set of the second argument in the finite-dimensional
`φ`-divergence. -/
noncomputable def coordinatePhiDivergenceZeroIndices {N : ℕ} (y : Fin N → ℝ) :
    Finset (Fin N) :=
  Finset.univ.filter fun i ↦ y i = 0

/-- The positive-coordinate index set of the second argument in the finite-dimensional
`φ`-divergence. -/
noncomputable def coordinatePhiDivergencePositiveIndices {N : ℕ} (y : Fin N → ℝ) :
    Finset (Fin N) :=
  Finset.univ.filter fun i ↦ 0 < y i

/-- The finite-dimensional `φ`-divergence on the canonical `Fin N → ℝ` model of `ℝ^N × ℝ^N`,
obtained by pulling back the chapter's finite direct-sum owner along the canonical coordinate view
of the family `i ↦ (y i, x i)`. -/
noncomputable def coordinatePhiDivergence (N : ℕ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain φ).Nonempty) :
    ((Fin N → ℝ) × (Fin N → ℝ)) → Set.Ioi (⊥ : EReal) :=
  directSumFunction (fun _ : Fin N ↦ closedPerspective φ hdom) ∘
    fun p ↦ Equiv.lpPiLp.symm (WithLp.toLp 2 fun i ↦ (p.2 i, p.1 i))

/-- Helper for Example 9.46: pairing the two coordinate families produces the family of swapped
scalar pairs used by the scalar closed perspective. -/
private noncomputable def coordinate_pair_linear_equiv (N : ℕ) :
    ((Fin N → ℝ) × (Fin N → ℝ)) ≃ₗ[ℝ] (Fin N → ℝ × ℝ) where
  toFun := fun p i ↦ (p.2 i, p.1 i)
  invFun := fun z ↦ (fun i ↦ (z i).2, fun i ↦ (z i).1)
  left_inv := by
    -- Reading back the second and first coordinates recovers the original pair of families.
    intro p
    ext i <;> rfl
  right_inv := by
    -- Pairing the recovered coordinates returns the original family of pairs.
    intro z
    ext i <;> rfl
  map_add' := by
    -- The coordinatewise pairing map is additive in each family.
    intro p q
    ext i <;> rfl
  map_smul' := by
    -- Scalar multiplication also acts coordinatewise on the paired family.
    intro a p
    ext i <;> rfl

/-- Helper for Example 9.46: the canonical continuous linear equivalence from the coordinate model
`ℝ^N × ℝ^N` to the `lp` owner space used by the finite direct-sum theorem. -/
noncomputable def coordinate_pair_to_lp_equiv (N : ℕ) :
    ((Fin N → ℝ) × (Fin N → ℝ)) ≃L[ℝ] lp (fun _ : Fin N ↦ ℝ × ℝ) 2 :=
  (coordinate_pair_linear_equiv N).toContinuousLinearEquiv.trans
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ × ℝ)).symm.trans
      ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ × ℝ) ℝ).symm.toContinuousLinearEquiv))

/-- Helper for Example 9.46: the canonical coordinate/swap map as an unbundled function. -/
noncomputable abbrev coordinate_pair_to_lp (N : ℕ) :
    ((Fin N → ℝ) × (Fin N → ℝ)) → lp (fun _ : Fin N ↦ ℝ × ℝ) 2 :=
  coordinate_pair_to_lp_equiv N

/-- Helper for Example 9.46: the coordinate divergence is exactly the direct-sum owner composed
with the canonical coordinate/swap map. -/
theorem coordinatePhiDivergence_eq_directSum_comp_coordinate_pair_to_lp (N : ℕ)
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty) :
    coordinatePhiDivergence N φ hdom =
      directSumFunction (fun _ : Fin N ↦ closedPerspective φ hdom) ∘
        coordinate_pair_to_lp N := by
  -- Both sides are the same definition written through the bundled coordinate map.
  rfl

/-- Helper for Example 9.46: the sum of two lower semicontinuous `EReal`-valued functions is
lower semicontinuous. -/
private theorem lowerSemicontinuous_add_ereal_local
    {H : Type*} [TopologicalSpace H] {g h : H → EReal}
    (hg : LowerSemicontinuous g) (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (fun x ↦ g x + h x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  -- Compare the pointwise sum with the liminf of the two summands separately.
  calc
    g x + h x ≤ Filter.liminf g (nhds x) + Filter.liminf h (nhds x) :=
      add_le_add (hg.le_liminf x) (hh.le_liminf x)
    _ ≤ Filter.liminf (fun y ↦ g y + h y) (nhds x) := by
      simpa using (EReal.le_liminf_add :
        Filter.liminf g (nhds x) + Filter.liminf h (nhds x) ≤
          Filter.liminf (g + h) (nhds x))

/-- Helper for Example 9.46: a finite sum of lower semicontinuous `EReal`-valued functions is
lower semicontinuous. -/
private theorem lowerSemicontinuous_finset_sum_ereal_local
    {ι : Type*} {H : Type*} [TopologicalSpace H] (s : Finset ι) (g : ι → H → EReal)
    (hg : ∀ i ∈ s, LowerSemicontinuous (g i)) :
    LowerSemicontinuous (fun x ↦ ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : H ↦ (0 : EReal)))
  | @insert i s hi ih =>
      have hi_term : LowerSemicontinuous (g i) := hg i (Finset.mem_insert_self i s)
      have hs_sum : LowerSemicontinuous (fun x ↦ ∑ j ∈ s, g j x) :=
        ih (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))
      -- Rewrite the inserted sum as a pointwise addition and apply the two-function lemma.
      simpa [Finset.sum_insert, hi] using lowerSemicontinuous_add_ereal_local hi_term hs_sum

/-- Helper for Example 9.46: if every summand is finite, then the whole finite `EReal` sum is
finite. -/
private theorem finset_sum_lt_top_of_forall_lt_top
    {ι : Type*} (s : Finset ι) (g : ι → EReal) (hg : ∀ i ∈ s, g i < ⊤) :
    ∑ i ∈ s, g i < ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact EReal.add_lt_top
        (ne_of_lt (hg i (Finset.mem_insert_self i s)))
        (ne_of_lt (ih (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))))

/-- Helper for Example 9.46: one `⊤` summand forces the whole finite `EReal` sum to be `⊤`. -/
private theorem finset_sum_ne_bot_of_forall_ne_bot
    {ι : Type*} (s : Finset ι) (g : ι → EReal) (hg : ∀ i ∈ s, g i ≠ ⊥) :
    ∑ j ∈ s, g j ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, EReal.add_ne_bot_iff]
      constructor
      · exact hg i (Finset.mem_insert_self i s)
      · exact ih (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))

/-- Helper for Example 9.46: one `⊤` summand forces the whole finite `EReal` sum to be `⊤`. -/
private theorem finset_sum_eq_top_of_mem_eq_top
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → EReal) {i : ι}
    (hi : i ∈ s) (hgi : g i = ⊤) (hbot : ∀ j ∈ s.erase i, g j ≠ ⊥) :
    ∑ j ∈ s, g j = ⊤ := by
  classical
  -- Isolate the `⊤` summand and collapse the rest with `⊤ + a = ⊤`.
  calc
    ∑ j ∈ s, g j = g i + ∑ j ∈ s.erase i, g j := by
      symm
      exact Finset.add_sum_erase s g hi
    _ = ⊤ + ∑ j ∈ s.erase i, g j := by
      rw [hgi]
    _ = ⊤ := by
      have hsum_ne_bot :
          ∑ j ∈ s.erase i, g j ≠ ⊥ :=
        finset_sum_ne_bot_of_forall_ne_bot (s.erase i) g hbot
      simpa using EReal.top_add_of_ne_bot hsum_ne_bot

/-- Helper for Example 9.46: a nonnegative finite `EReal` scalar distributes over a finite sum. -/
private theorem ereal_mul_finset_sum_of_nonneg_of_ne_top
    {ι : Type*} (s : Finset ι) (a : EReal) (ha_nonneg : 0 ≤ a) (ha_top : a ≠ ⊤) (g : ι → EReal) :
    a * ∑ i ∈ s, g i = ∑ i ∈ s, a * g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_top, ih]

/-- Helper for Example 9.46: a constant family of scalar `Γ₀` integrands still belongs to `Γ₀`
after taking the finite direct sum over `Fin N`. -/
theorem directSum_const_mem_gammaZero (N : ℕ)
    {f : (ℝ × ℝ) → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(ℝ × ℝ)) :
    directSumFunction (fun _ : Fin N ↦ f) ∈ Γ₀(lp (fun _ : Fin N ↦ ℝ × ℝ) 2) := by
  rw [mem_gammaZero_iff]
  constructor
  · have hterm :
        ∀ i : Fin N,
          LowerSemicontinuous
            (fun x : lp (fun _ : Fin N ↦ ℝ × ℝ) 2 ↦ (f (x i) : EReal)) := by
      intro i
      have hcont : Continuous (fun x : lp (fun _ : Fin N ↦ ℝ × ℝ) 2 ↦ x i) := by
        exact ((@continuous_apply (Fin N) (fun j ↦ ℝ × ℝ) _ i).comp
          ((lp.uniformContinuous_coe (E := fun _ : Fin N ↦ ℝ × ℝ)
            (p := (2 : ENNReal))).continuous))
      -- Each coordinate term is the scalar `Γ₀` integrand composed with a continuous evaluation
      -- map.
      change LowerSemicontinuous ((fun y : ℝ × ℝ ↦ (f y : EReal)) ∘
        fun x : lp (fun _ : Fin N ↦ ℝ × ℝ) 2 ↦ x i)
      simpa [Function.comp] using (mem_gammaZero_iff.mp hf).1.comp hcont
    have hsum :
        LowerSemicontinuous
          (fun x : lp (fun _ : Fin N ↦ ℝ × ℝ) 2 ↦ ∑ i, (f (x i) : EReal)) := by
      simpa using
        (lowerSemicontinuous_finset_sum_ereal_local
          (s := (Finset.univ : Finset (Fin N)))
          (g := fun i (x : lp (fun _ : Fin N ↦ ℝ × ℝ) 2) ↦ (f (x i) : EReal))
          (hg := by
            intro i hi
            exact hterm i))
    simpa [directSumFunction_apply] using hsum
  · refine ⟨?_, subset_rfl, ?_⟩
    · rcases (mem_gammaZero_iff.mp hf).2.nonempty with ⟨p, hp⟩
      let x₀ : lp (fun _ : Fin N ↦ ℝ × ℝ) 2 :=
        Equiv.lpPiLp.symm (WithLp.toLp 2 fun _ : Fin N ↦ p)
      refine ⟨x₀, ?_⟩
      rw [mem_effectiveDomain_iff, directSumFunction_apply]
      have hp_finite : (f p : EReal) < ⊤ :=
        mem_effectiveDomain_iff.mp ((mem_gammaZero_iff.mp hf).2.subset_effectiveDomain hp)
      -- Every coordinate of the constant witness contributes the same finite scalar value.
      exact finset_sum_lt_top_of_forall_lt_top Finset.univ
        (fun i : Fin N ↦ (f (((x₀ : lp (fun _ : Fin N ↦ ℝ × ℝ) 2) : Fin N → ℝ × ℝ) i) : EReal))
        (by
          intro i hi
          simpa [x₀] using hp_finite)
    · intro x hx y hy α hα0 hα1
      have hxsum : (∑ i, (f (x i) : EReal)) < ⊤ := by
        simpa [directSumFunction_apply] using hx
      have hysum : (∑ i, (f (y i) : EReal)) < ⊤ := by
        simpa [directSumFunction_apply] using hy
      have hxcoord : ∀ i : Fin N, x i ∈ effectiveDomain f := by
        intro i
        rw [mem_effectiveDomain_iff]
        by_contra hxi
        have hxi_top : (f (x i) : EReal) = ⊤ := by
          exact le_antisymm le_top (le_of_not_gt hxi)
        have htop :
            ∑ j, (f (x j) : EReal) = ⊤ :=
          finset_sum_eq_top_of_mem_eq_top Finset.univ
            (fun j : Fin N ↦ (f (x j) : EReal)) (by simp) hxi_top
            (fun j hj ↦ (f (x j)).2.ne')
        exact (ne_of_lt hxsum) htop
      have hycoord : ∀ i : Fin N, y i ∈ effectiveDomain f := by
        intro i
        rw [mem_effectiveDomain_iff]
        by_contra hyi
        have hyi_top : (f (y i) : EReal) = ⊤ := by
          exact le_antisymm le_top (le_of_not_gt hyi)
        have htop :
            ∑ j, (f (y j) : EReal) = ⊤ :=
          finset_sum_eq_top_of_mem_eq_top Finset.univ
            (fun j : Fin N ↦ (f (y j) : EReal)) (by simp) hyi_top
            (fun j hj ↦ (f (y j)).2.ne')
        exact (ne_of_lt hysum) htop
      have hαE_nonneg : 0 ≤ (α : EReal) := by
        exact_mod_cast hα0.le
      have hαE_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top α
      have hβE_nonneg : 0 ≤ (1 - α : EReal) := by
        exact_mod_cast (sub_nonneg.mpr hα1.le)
      have hβE_ne_top : (1 - α : EReal) ≠ ⊤ := EReal.coe_ne_top (1 - α)
      -- Apply the scalar Jensen inequality coordinatewise and sum the resulting inequalities.
      calc
        (directSumFunction (fun _ : Fin N ↦ f) (α • x + (1 - α) • y) : EReal)
            = ∑ i, (f (α • x i + (1 - α) • y i) : EReal) := by
                rw [directSumFunction_apply]
                refine Finset.sum_congr rfl ?_
                intro i hi
                rfl
        _ ≤ ∑ i, ((α : EReal) * (f (x i) : EReal) + (1 - α : EReal) * (f (y i) : EReal)) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact (mem_gammaZero_iff.mp hf).2.ineq (hxcoord i) (hycoord i) hα0 hα1
        _ = (∑ i, (α : EReal) * (f (x i) : EReal)) +
              ∑ i, (1 - α : EReal) * (f (y i) : EReal) := by
              rw [Finset.sum_add_distrib]
        _ = (α : EReal) * ∑ i, (f (x i) : EReal) +
              ∑ i, (1 - α : EReal) * (f (y i) : EReal) := by
              congr 1
              simpa using
                (ereal_mul_finset_sum_of_nonneg_of_ne_top
                  (s := (Finset.univ : Finset (Fin N))) (a := (α : EReal))
                  hαE_nonneg hαE_ne_top (g := fun i : Fin N ↦ (f (x i) : EReal))).symm
        _ = (α : EReal) * ∑ i, (f (x i) : EReal) +
              (1 - α : EReal) * ∑ i, (f (y i) : EReal) := by
              congr 1
              simpa using
                (ereal_mul_finset_sum_of_nonneg_of_ne_top
                  (s := (Finset.univ : Finset (Fin N))) (a := (1 - α : EReal))
                  hβE_nonneg hβE_ne_top (g := fun i : Fin N ↦ (f (y i) : EReal))).symm
        _ = (α : EReal) * (directSumFunction (fun _ : Fin N ↦ f) x : EReal) +
              (1 - α : EReal) * (directSumFunction (fun _ : Fin N ↦ f) y : EReal) := by
              rw [directSumFunction_apply, directSumFunction_apply]

/-- Coercing `coordinatePhiDivergence` to `EReal` recovers the summed closed-perspective formula. -/
@[simp] theorem coordinatePhiDivergence_apply (N : ℕ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain φ).Nonempty) (p : (Fin N → ℝ) × (Fin N → ℝ)) :
    (coordinatePhiDivergence N φ hdom p : EReal) =
      ∑ i, (closedPerspective φ hdom (p.2 i, p.1 i) : EReal) := by
  let y : PiLp 2 (fun _ : Fin N ↦ ℝ × ℝ) := WithLp.toLp 2 fun i ↦ (p.2 i, p.1 i)
  have hy :
      ((Equiv.lpPiLp.symm y : lp (fun _ : Fin N ↦ ℝ × ℝ) 2) : Fin N → ℝ × ℝ) = y :=
    coe_equiv_lpPiLp_symm y
  -- Rewrite the direct sum through the canonical `lp`/`PiLp` equivalence and then read off the
  -- paired coordinates.
  calc
    (coordinatePhiDivergence N φ hdom p : EReal)
        = ∑ i, (closedPerspective φ hdom
            (((Equiv.lpPiLp.symm y : lp (fun _ : Fin N ↦ ℝ × ℝ) 2) :
              Fin N → ℝ × ℝ) i) : EReal) := by
            simp [coordinatePhiDivergence, directSumFunction_apply, y]
    _ = ∑ i, (closedPerspective φ hdom (y i) : EReal) := by
          simp [hy]
    _ = ∑ i, (closedPerspective φ hdom (p.2 i, p.1 i) : EReal) := by
          simp [y]

/-- The finite-dimensional `φ`-divergence is given by the textbook formula with recession terms on
the zero coordinates of `y`, perspective terms on the positive coordinates, and value `+∞` as soon
as one coordinate of `y` is negative. -/
theorem coordinatePhiDivergence_eq_textbook_formula (N : ℕ)
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty)
    (x y : Fin N → ℝ) :
    (coordinatePhiDivergence N φ hdom (x, y) : EReal) =
      if coordinatePhiDivergenceNegativeIndices y = ∅ then
        (∑ i ∈ coordinatePhiDivergenceZeroIndices y,
          (recessionFunction φ hdom (x i) : EReal)) +
        (∑ i ∈ coordinatePhiDivergencePositiveIndices y,
          (y i : EReal) * (φ (x i / y i) : EReal))
      else
        ⊤ := by
  by_cases hneg : coordinatePhiDivergenceNegativeIndices y = ∅
  · -- With no negative coordinates, each summand is either the recession term or the positive
    -- perspective term, so split the finite sum according to the zero coordinates.
    rw [if_pos hneg, coordinatePhiDivergence_apply]
    simp [closedPerspective_coe]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N ↦ y i = 0)
      (fun i ↦ closedPerspectiveEReal φ hdom (y i, x i))]
    have hpos_filter :
        Finset.univ.filter (fun i : Fin N ↦ ¬ y i = 0) =
          coordinatePhiDivergencePositiveIndices y := by
      ext i
      constructor
      · intro hi
        have hi_ne : y i ≠ 0 := by
          simpa using hi
        have hnotneg : ¬ y i < 0 := by
          intro hy_neg
          have hi_neg : i ∈ coordinatePhiDivergenceNegativeIndices y := by
            simp [coordinatePhiDivergenceNegativeIndices, hy_neg]
          rw [hneg] at hi_neg
          simp at hi_neg
        have hy_nonneg : 0 ≤ y i := le_of_not_gt hnotneg
        have hy_pos : 0 < y i := lt_of_le_of_ne hy_nonneg (Ne.symm hi_ne)
        simpa [coordinatePhiDivergencePositiveIndices, hy_pos]
      · intro hi
        have hy_pos : 0 < y i := by
          simpa [coordinatePhiDivergencePositiveIndices] using hi
        have hi_ne : y i ≠ 0 := ne_of_gt hy_pos
        simpa [hi_ne] using hi
    have hzero_sum :
        ∑ i ∈ coordinatePhiDivergenceZeroIndices y,
            closedPerspectiveEReal φ hdom (y i, x i) =
          ∑ i ∈ coordinatePhiDivergenceZeroIndices y,
            (recessionFunction φ hdom (x i) : EReal) := by
      -- On the zero slice, each scalar closed perspective is exactly the recession function.
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hy_zero : y i = 0 := by
        simpa [coordinatePhiDivergenceZeroIndices] using hi
      simpa [hy_zero] using
        (closedPerspectiveEReal_apply_zero φ hdom (x i))
    have hpositive_sum :
        ∑ i ∈ coordinatePhiDivergencePositiveIndices y,
            closedPerspectiveEReal φ hdom (y i, x i) =
          ∑ i ∈ coordinatePhiDivergencePositiveIndices y,
            (y i : EReal) * (φ (x i / y i) : EReal) := by
      -- On strictly positive coordinates, the scalar closed perspective is the usual perspective.
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hy_pos : 0 < y i := by
        simpa [coordinatePhiDivergencePositiveIndices] using hi
      have hy_ne : y i ≠ 0 := ne_of_gt hy_pos
      rw [closedPerspectiveEReal_apply_of_ne_zero (φ := φ) (hdom := hdom) hy_ne,
        perspective_apply_of_pos (fun z : ℝ ↦ (φ z : EReal)) hy_pos]
      simp [div_eq_mul_inv, mul_comm]
    -- Replace the two filtered sums by the textbook zero and positive index sets.
    simpa [coordinatePhiDivergenceZeroIndices, hpos_filter] using
      congrArg₂ (· + ·) hzero_sum hpositive_sum
  · -- A single negative coordinate already forces one scalar summand to be `⊤`, so the whole
    -- finite sum is `⊤`.
    rw [if_neg hneg, coordinatePhiDivergence_apply]
    simp [closedPerspective_coe]
    rcases Finset.nonempty_iff_ne_empty.mpr hneg with ⟨i, hi⟩
    have hy_neg : y i < 0 := by
      simpa [coordinatePhiDivergenceNegativeIndices] using hi
    have hy_ne : y i ≠ 0 := ne_of_lt hy_neg
    have htop_i : closedPerspectiveEReal φ hdom (y i, x i) = ⊤ := by
      rw [closedPerspectiveEReal_apply_of_ne_zero (φ := φ) (hdom := hdom) hy_ne,
        perspective_apply_of_nonpos (fun z : ℝ ↦ (φ z : EReal)) (le_of_lt hy_neg)]
    -- Isolate the negative coordinate and collapse the remaining sum with `⊤ + a = ⊤`.
    calc
      ∑ j, closedPerspectiveEReal φ hdom (y j, x j)
          = closedPerspectiveEReal φ hdom (y i, x i) +
              Finset.sum (Finset.univ.erase i)
                (fun j : Fin N ↦ closedPerspectiveEReal φ hdom (y j, x j)) := by
            symm
            exact Finset.add_sum_erase Finset.univ
              (fun j : Fin N ↦ closedPerspectiveEReal φ hdom (y j, x j)) (by simp)
      _ = ⊤ + Finset.sum (Finset.univ.erase i)
            (fun j : Fin N ↦ closedPerspectiveEReal φ hdom (y j, x j)) := by
            rw [htop_i]
      _ = ⊤ := by
            have hsum_ne_bot :
                Finset.sum (Finset.univ.erase i)
                  (fun j : Fin N ↦ closedPerspectiveEReal φ hdom (y j, x j)) ≠ ⊥ :=
              finset_sum_ne_bot_of_forall_ne_bot (Finset.univ.erase i)
                (fun j : Fin N ↦ closedPerspectiveEReal φ hdom (y j, x j))
                (fun j hj ↦ (closedPerspectiveEReal_ne_bot φ hdom (y j, x j)).ne')
            simpa using EReal.top_add_of_ne_bot hsum_ne_bot

-- Proof sketch: Proposition 9.42 gives
-- `closedPerspective φ hφ.2.nonempty ∈ Γ₀(ℝ × ℝ)`. The function
-- `coordinatePhiDivergence N φ hφ.2.nonempty` is the finite direct sum of this same coordinate
-- function over
-- the index type `Fin N`, so Remark 9.37 yields membership in `Γ₀` for the product space
-- `ℝ^N × ℝ^N`.
/-- Example 9.46: for `φ ∈ Γ₀(ℝ)`, the finite-dimensional function `d_φ` obtained by summing the
scalar closed perspective coordinatewise on the canonical `Fin N → ℝ` model of `ℝ^N × ℝ^N`
belongs to `Γ₀(ℝ^N × ℝ^N)`. -/
theorem coordinatePhiDivergence_mem_gammaZero (N : ℕ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(ℝ)) :
    coordinatePhiDivergence N φ hφ.2.nonempty ∈ Γ₀((Fin N → ℝ) × (Fin N → ℝ)) := by
  let ψ : ℝ × ℝ → Set.Ioi (⊥ : EReal) := closedPerspective φ hφ.2.nonempty
  have hψ : ψ ∈ Γ₀(ℝ × ℝ) := by
    -- Proposition 9.42 is the scalar owner statement used at every coordinate.
    simpa [ψ] using closedPerspective_mem_gammaZero φ hφ
  have hdirectSum :
      directSumFunction (fun _ : Fin N ↦ ψ) ∈
        Γ₀(lp (fun _ : Fin N ↦ ℝ × ℝ) 2) := by
    -- The constant-family case is the direct-sum statement needed by the textbook proof.
    simpa [ψ] using directSum_const_mem_gammaZero N hψ
  let F : lp (fun _ : Fin N ↦ ℝ × ℝ) 2 → Set.Ioi (⊥ : EReal) :=
    directSumFunction (fun _ : Fin N ↦ ψ)
  have hpullback :
      F ∘
          coordinate_pair_to_lp N ∈ Γ₀((Fin N → ℝ) × (Fin N → ℝ)) :=
    mem_gammaZero_comp_continuousLinearEquiv (f := F) (by simpa [F] using hdirectSum)
      (coordinate_pair_to_lp_equiv N)
  -- The coordinate model is just the direct-sum owner transported through the canonical
  -- coordinate/swap equivalence.
  simpa [coordinatePhiDivergence_eq_directSum_comp_coordinate_pair_to_lp, ψ, F] using hpullback

end ERealFunction
