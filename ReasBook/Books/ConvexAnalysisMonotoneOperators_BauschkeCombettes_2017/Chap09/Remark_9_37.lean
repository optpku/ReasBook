/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

namespace ERealFunction

section CoordinateSlice

variable {I : Type v} [Finite I]
variable {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)]

/-- A coordinate slice through a base family changes only the `i`th coordinate and packages the
resulting family as an element of the finite Hilbert direct sum. -/
noncomputable def coordinateSlice (x : ∀ i, H i) (i : I) (y : H i) : lp H 2 :=
  let _ : DecidableEq I := Classical.decEq I
  ⟨Function.update x i y, Memℓp.all _⟩

/-- Evaluating the updated coordinate of a coordinate slice returns the inserted value. -/
@[simp] theorem coordinateSlice_apply_self (x : ∀ i, H i) (i : I) (y : H i) :
    coordinateSlice x i y i = y := by
  classical
  simp [coordinateSlice]

/-- Away from the distinguished index, a coordinate slice agrees with the base family. -/
@[simp] theorem coordinateSlice_apply_of_ne (x : ∀ i, H i) {i j : I} (hji : j ≠ i) (y : H i) :
    coordinateSlice x i y j = x j := by
  classical
  simp [coordinateSlice, Function.update, hji]

end CoordinateSlice

section CoordinateSliceEuclidean

variable {N : ℕ}

/-- The Euclidean-space specialization of `coordinateSlice`, obtained by transporting the
finite-coordinate `ℓ²` slice through the canonical identification
`ℓ²(Fin N, ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)`. -/
noncomputable abbrev coordinateSliceEuclidean (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) (y : ℝ) :
    EuclideanSpace ℝ (Fin N) :=
  (lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ) (coordinateSlice x.ofLp i y)

/-- Evaluating the active coordinate of a Euclidean coordinate slice returns the inserted value. -/
@[simp] theorem coordinateSliceEuclidean_apply_self
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) (y : ℝ) :
    coordinateSliceEuclidean x i y i = y := by
  change (coordinateSlice x.ofLp i y : Fin N → ℝ) i = y
  simp

/-- Away from the distinguished index, a Euclidean coordinate slice agrees with the base point. -/
@[simp] theorem coordinateSliceEuclidean_apply_of_ne
    (x : EuclideanSpace ℝ (Fin N)) {i j : Fin N} (hji : j ≠ i) (y : ℝ) :
    coordinateSliceEuclidean x i y j = x j := by
  change (coordinateSlice x.ofLp i y : Fin N → ℝ) j = x j
  simp [hji]

end CoordinateSliceEuclidean

attribute [local instance] Classical.decEq

variable {I : Type v} [Fintype I]
variable {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)]

/-- Helper for Remark 9.37: over a finite index set, a sum of values in `]-∞,+∞]` still avoids
`-∞`. -/
-- Proof sketch: induct over the finite set and use that `EReal` addition preserves the
-- non-`⊥` property.
private theorem finset_sum_mem_Ioi_bot (s : Finset I) (a : I → Set.Ioi (⊥ : EReal)) :
    (∑ i ∈ s, (a i : EReal)) ∈ Set.Ioi (⊥ : EReal) := by
  classical
  have hne : (∑ i ∈ s, (a i : EReal)) ≠ ⊥ := by
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert i s hi ih =>
        simpa [Finset.sum_insert, hi] using
          (EReal.add_ne_bot_iff.2 ⟨ne_of_gt (a i).2, ih⟩)
  exact lt_of_le_of_ne bot_le hne.symm

/-- Helper for Remark 9.37: for a finite family of values in `]-∞,+∞]`, finiteness of the total
sum is equivalent to finiteness of each summand. -/
-- Proof sketch: induct over the finite set and apply `EReal.add_ne_top_iff_ne_top₂`, using the
-- previous non-`⊥` lemma to justify the induction step.
private theorem finset_sum_lt_top_iff (s : Finset I) (a : I → Set.Ioi (⊥ : EReal)) :
    (∑ i ∈ s, (a i : EReal)) < ⊤ ↔ ∀ i ∈ s, (a i : EReal) < ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hsum_ne_bot : (∑ j ∈ s, (a j : EReal)) ≠ ⊥ :=
        ne_of_gt (finset_sum_mem_Ioi_bot (s := s) a)
      have hai_ne_bot : (a i : EReal) ≠ ⊥ := ne_of_gt (a i).2
      have ih' : (∑ j ∈ s, (a j : EReal)) ≠ ⊤ ↔ ∀ j ∈ s, (a j : EReal) < ⊤ := by
        rw [← lt_top_iff_ne_top, ih]
      rw [Finset.sum_insert hi, lt_top_iff_ne_top,
        EReal.add_ne_top_iff_ne_top₂ hai_ne_bot hsum_ne_bot, ih']
      constructor
      · intro h j hj
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact lt_top_iff_ne_top.mpr h.1
        · exact h.2 j hj'
      · intro h
        constructor
        · exact lt_top_iff_ne_top.mp (h i (Finset.mem_insert_self i s))
        · intro j hj
          exact h j (Finset.mem_insert_of_mem hj)

/-- A finite sum of values in `]-∞,+∞]` still lies in `]-∞,+∞]`. -/
-- Proof sketch: induct on a finite enumeration of the index type and use that `EReal` addition
-- preserves the strict inequality above `⊥`.
theorem fintype_sum_mem_Ioi_bot (a : I → Set.Ioi (⊥ : EReal)) :
    (∑ i, (a i : EReal)) ∈ Set.Ioi (⊥ : EReal) := by
  -- The finite-type statement is the `Finset.univ` specialization of the finite-set helper.
  simpa using finset_sum_mem_Ioi_bot (s := (Finset.univ : Finset I)) a

/-- The direct-sum function attached to a finite family of proper coordinate functions on a Hilbert
direct sum is the pointwise sum of the coordinate values. -/
noncomputable def directSumFunction (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) :
    lp H 2 → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨∑ i, (f i (x i) : EReal), fintype_sum_mem_Ioi_bot (fun i ↦ f i (x i))⟩

/-- Coercing `directSumFunction` to `EReal` recovers the ordinary finite sum of the coordinate
functions. -/
@[simp] theorem directSumFunction_apply (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (x : lp H 2) :
    (directSumFunction f x : EReal) = ∑ i, (f i (x i) : EReal) := rfl

section Hilbert

variable [∀ i, InnerProductSpace ℝ (H i)]

/-- The `EReal` coercion of `directSumFunction` agrees with the finite-branch specialization of the
general Hilbert direct-sum function from Proposition 8.6. -/
-- Proof sketch: unfold `directSumFunction`, then simplify the finite branch of
-- `hilbertSumFunction` using `hilbertSumFunction_apply_of_finite`.
@[simp] theorem directSumFunction_coe_eq_hilbertSumFunction
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (x : lp H 2) :
    (directSumFunction f x : EReal) =
      hilbertSumFunction (fun i xi ↦ (f i xi : EReal)) x := by
  -- In the finite branch, both constructions are the same ordinary sum over `Finset.univ`.
  have hI : Finite I := by infer_instance
  simp [hilbertSumFunction, hI, directSumFunction_apply]
  have huniv : (@Finset.univ I inferInstance) = (@Finset.univ I (Fintype.ofFinite I)) := by
    ext i
    simp
  simpa using congrArg (fun s : Finset I ↦ s.sum (fun i ↦ (f i (x i) : EReal))) huniv

/-- Helper for Remark 9.37: the finite sum of coordinate values on effective-domain points is the
cast of the corresponding real sum of `toReal` values. -/
-- Proof sketch: induct over the finite set and replace each summand by its `toReal` cast using
-- effective-domain finiteness.
private theorem finset_sum_eq_coe_toReal
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (s : Finset I) (x : ∀ i, H i)
    (hx : ∀ i ∈ s, x i ∈ effectiveDomain (f i)) :
    (∑ i ∈ s, (f i (x i) : EReal)) =
      ((∑ i ∈ s, (f i (x i) : EReal).toReal : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is already the cast of the zero real sum.
      simp
  | @insert i s hi ih =>
      have hi_top : (f i (x i) : EReal) ≠ ⊤ := by
        exact ne_of_lt ((mem_effectiveDomain_iff).mp (hx i (Finset.mem_insert_self i s)))
      have hi_bot : (f i (x i) : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f i (x i) : EReal) from (f i (x i)).2)
      -- Peel off the distinguished summand and convert it with `EReal.coe_toReal`.
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih]
      · conv_lhs => rw [← EReal.coe_toReal hi_top hi_bot]
        rw [← EReal.coe_add]
      · intro j hj
        exact hx j (Finset.mem_insert_of_mem hj)

/-- Helper for Remark 9.37: membership in the effective domain of the finite direct sum is exactly
coordinatewise membership in the effective domains. -/
-- Proof sketch: rewrite the direct sum as an ordinary finite `EReal` sum and apply the finite-sum
-- finiteness criterion above.
private theorem directSumFunction_mem_effectiveDomain_iff
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (x : lp H 2) :
    x ∈ effectiveDomain (directSumFunction f) ↔ ∀ i, x i ∈ effectiveDomain (f i) := by
  -- Route correction: the total direct-sum value is finite exactly when each coordinate term is.
  rw [mem_effectiveDomain_iff, directSumFunction_apply,
    finset_sum_lt_top_iff (s := (Finset.univ : Finset I)) (a := fun i ↦ f i (x i))]
  constructor
  · intro hx i
    exact hx i (by simp)
  · intro hx i hi
    exact hx i

/-- Helper for Remark 9.37: properness of every coordinate function gives a nonempty effective
domain for the finite direct sum. -/
-- Proof sketch: choose one effective-domain point in each coordinate and package the resulting
-- family as an `lp H 2` element.
private theorem directSumFunction_effectiveDomain_nonempty_of_proper
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hproper : ∀ i, IsProper (fun x : H i ↦ (f i x : EReal))) :
    (effectiveDomain (directSumFunction f)).Nonempty := by
  classical
  let x₀ : ∀ i, H i := fun i ↦ Classical.choose (hproper i).2
  have hx₀ : ∀ i, x₀ i ∈ effectiveDomain (f i) := by
    intro i
    simpa [dom, effectiveDomain] using (Classical.choose_spec (hproper i).2)
  refine ⟨⟨x₀, Memℓp.all x₀⟩, ?_⟩
  simpa [directSumFunction_mem_effectiveDomain_iff] using hx₀

/-- Helper for Remark 9.37: taking the same convex combination of two coordinate slices gives the
slice through the convex combination in that coordinate. -/
-- Proof sketch: compare coordinates one by one; outside the distinguished index the coefficients
-- sum to `1`, while at the distinguished index the updated coordinate is exactly the desired
-- convex combination.
private theorem coordinateSlice_convexCombination
    (x₀ : ∀ i, H i) (i : I) (x y : H i) (α : ℝ) :
    α • coordinateSlice x₀ i x + (1 - α) • coordinateSlice x₀ i y =
      coordinateSlice x₀ i (α • x + (1 - α) • y) := by
  -- Compare coordinates directly; only the distinguished coordinate changes.
  ext j
  by_cases hj : j = i
  · subst hj
    change (α • Function.update x₀ j x + (1 - α) • Function.update x₀ j y) j =
      Function.update x₀ j (α • x + (1 - α) • y) j
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    simp
  · change (α • Function.update x₀ i x + (1 - α) • Function.update x₀ i y) j =
      Function.update x₀ i (α • x + (1 - α) • y) j
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    simp [Function.update, hj]

/-- Helper for Remark 9.37: on a slice through a fixed base family, the direct sum is the active
coordinate value plus a constant real-cast contribution from the frozen coordinates. -/
-- Proof sketch: split the finite sum into the distinguished index and the erased remainder, then
-- turn the frozen remainder into a real cast via the previous `toReal` helper.
private theorem directSumFunction_coordinate_slice_apply
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (x₀ : ∀ i, H i)
    (hx₀ : ∀ i, x₀ i ∈ effectiveDomain (f i)) (i : I) (z : H i) :
    (directSumFunction f (coordinateSlice x₀ i z) : EReal) =
      (f i z : EReal) +
        ((∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal : ℝ) : EReal) := by
  have htail :
      (∑ j ∈ Finset.univ.erase i, (f j (Function.update x₀ i z j) : EReal)) =
        ((∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal : ℝ) : EReal) := by
    have hx_tail : ∀ j ∈ Finset.univ.erase i, Function.update x₀ i z j ∈ effectiveDomain (f j) := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simpa [Function.update, hji] using hx₀ j
    have htail_raw :=
      finset_sum_eq_coe_toReal (f := f) (s := Finset.univ.erase i)
        (x := Function.update x₀ i z) hx_tail
    have htail_toReal :
        (∑ j ∈ Finset.univ.erase i, (f j (Function.update x₀ i z j) : EReal).toReal : ℝ) =
          ∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [Function.update, hji]
    -- On the erased tail, every coordinate equals the frozen base point, so the sum is a real cast.
    calc
      (∑ j ∈ Finset.univ.erase i, (f j (Function.update x₀ i z j) : EReal))
          = ((∑ j ∈ Finset.univ.erase i, (f j (Function.update x₀ i z j) : EReal).toReal : ℝ) : EReal) :=
            htail_raw
      _ = ((∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal : ℝ) : EReal) := by
            rw [htail_toReal]
  -- Split the full finite sum into the active coordinate and the frozen tail.
  calc
    (directSumFunction f (coordinateSlice x₀ i z) : EReal)
        = ∑ j, (f j ((coordinateSlice x₀ i z) j) : EReal) := by
            rw [directSumFunction_apply]
    _ = (f i ((coordinateSlice x₀ i z) i) : EReal) +
          ∑ j ∈ Finset.univ.erase i, (f j ((coordinateSlice x₀ i z) j) : EReal) := by
            symm
            exact Finset.add_sum_erase (s := Finset.univ)
              (f := fun j ↦ (f j ((coordinateSlice x₀ i z) j) : EReal)) (by simp)
    _ = (f i z : EReal) +
          ∑ j ∈ Finset.univ.erase i, (f j (Function.update x₀ i z j) : EReal) := by
            simp [coordinateSlice]
    _ = (f i z : EReal) +
          ((∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal : ℝ) : EReal) := by
            rw [htail]

/-- Helper for Remark 9.37: a proper strictly convex `]-∞,+∞]`-valued function is convex on its
effective domain. -/
-- Proof sketch: properness supplies the required nonemptiness, and the weak Jensen inequality is
-- obtained from strict Jensen by splitting into the equal and distinct-point cases.
private theorem convexOn_effectiveDomain_of_strictlyConvex
    {K : Type*} [AddCommGroup K] [Module ℝ K]
    (g : K → Set.Ioi (⊥ : EReal))
    (hproper : IsProper (fun x : K ↦ (g x : EReal))) (hg : StrictlyConvex g) :
    ConvexOn g (effectiveDomain g) := by
  refine ⟨hproper.2, ?_, ?_⟩
  · -- The chosen set is the effective domain itself.
    intro x hx
    exact hx
  · intro x hx y hy α hα0 hα1
    by_cases hxy : x = y
    · subst y
      have hcombo : α • x + (1 - α) • x = x := by
        calc
          α • x + (1 - α) • x = (α + (1 - α)) • x := by rw [add_smul]
          _ = x := by simp
      have hα_nonneg : 0 ≤ (α : EReal) := by
        exact_mod_cast hα0.le
      have hβ_nonneg : 0 ≤ ((1 - α : ℝ) : EReal) := by
        exact_mod_cast (sub_nonneg.mpr hα1.le)
      have hsum : (α : EReal) + (1 - α : EReal) = 1 := by
        exact_mod_cast (show α + (1 - α : ℝ) = 1 by ring)
      have hweight :
          (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g x : EReal) = (g x : EReal) := by
        -- For equal points, the right-hand side collapses by distributivity and `α + (1 - α) = 1`.
        calc
          (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g x : EReal)
              = ((α : EReal) + (1 - α : EReal)) * (g x : EReal) := by
                  symm
                  exact EReal.right_distrib_of_nonneg hα_nonneg hβ_nonneg
          _ = (g x : EReal) := by rw [hsum, one_mul]
      simp [hcombo, hweight]
    · -- Distinct points satisfy the strict Jensen inequality, hence also the weak one.
      exact le_of_lt (hg hx hy hxy hα0 hα1)

/-- Helper for Remark 9.37: a nonnegative finite `EReal` scalar distributes over a finite sum. -/
-- Proof sketch: induct over the finite set and use the corresponding two-term distributivity
-- lemma for `EReal`.
private theorem ereal_mul_finset_sum_of_nonneg_of_ne_top
    (a : EReal) (ha_nonneg : 0 ≤ a) (ha_ne_top : a ≠ ⊤) (s : Finset I) (b : I → EReal) :
    a * ∑ i ∈ s, b i = ∑ i ∈ s, a * b i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top, ih]

/-- Helper for Remark 9.37: the sum of two lower semicontinuous `EReal`-valued functions is lower
semicontinuous. -/
-- Proof sketch: compare the value at a point with the sum of the two liminfs and then use the
-- standard `EReal` liminf-add estimate.
private theorem lowerSemicontinuous_add_ereal
    {X : Type*} [TopologicalSpace X] {g h : X → EReal}
    (hg : LowerSemicontinuous g) (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (fun x ↦ g x + h x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  calc
    g x + h x ≤ Filter.liminf g (nhds x) + Filter.liminf h (nhds x) :=
      add_le_add (hg.le_liminf x) (hh.le_liminf x)
    _ ≤ Filter.liminf (fun y ↦ g y + h y) (nhds x) := by
      simpa using (EReal.le_liminf_add :
        Filter.liminf g (nhds x) + Filter.liminf h (nhds x) ≤
          Filter.liminf (g + h) (nhds x))

/-- Helper for Remark 9.37: a finite sum of lower semicontinuous `EReal`-valued functions is
lower semicontinuous. -/
-- Proof sketch: induct over the finite set, adding one lower semicontinuous term at a time.
private theorem lowerSemicontinuous_finset_sum_ereal
    {X : Type*} [TopologicalSpace X] (s : Finset I) (g : I → X → EReal)
    (hg : ∀ i ∈ s, LowerSemicontinuous (g i)) :
    LowerSemicontinuous (fun x ↦ ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : X ↦ (0 : EReal)))
  | @insert i s hi ih =>
      have hi_term : LowerSemicontinuous (g i) := hg i (Finset.mem_insert_self i s)
      have hs_sum : LowerSemicontinuous (fun x ↦ ∑ j ∈ s, g j x) :=
        ih (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))
      simpa [Finset.sum_insert, hi] using lowerSemicontinuous_add_ereal hi_term hs_sum

/-- Helper for Remark 9.37: lower semicontinuity is preserved by the finite direct sum of the
coordinate functions. -/
-- Proof sketch: compose each coordinate function with the continuous coordinate projection on
-- `lp H 2`, then apply the finite weighted-sum lower-semicontinuity theorem with unit weights.
private theorem directSumFunction_lowerSemicontinuous
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hlsc : ∀ i, LowerSemicontinuous (fun x : H i ↦ (f i x : EReal))) :
    LowerSemicontinuous (fun x : lp H 2 ↦ (directSumFunction f x : EReal)) := by
  have hterm : ∀ i, LowerSemicontinuous (fun x : lp H 2 ↦ (f i (x i) : EReal)) := by
    intro i
    have hcont : Continuous (fun x : lp H 2 ↦ x i) := by
      simpa [Function.comp] using
        (@continuous_apply I (fun j ↦ H j) _ i).comp
          ((lp.uniformContinuous_coe (E := H) (p := (2 : ENNReal))).continuous)
    change LowerSemicontinuous ((fun y : H i ↦ (f i y : EReal)) ∘ fun x : lp H 2 ↦ x i)
    simpa [Function.comp] using (hlsc i).comp hcont
  have hsum :
      LowerSemicontinuous (fun x : lp H 2 ↦ ∑ i, (f i (x i) : EReal)) := by
    simpa using
      lowerSemicontinuous_finset_sum_ereal
        (s := (Finset.univ : Finset I))
        (g := fun i (x : lp H 2) ↦ (f i (x i) : EReal))
        (hg := fun i _ ↦ hterm i)
  simpa [directSumFunction_apply] using hsum

/-- Helper for Remark 9.37: canceling the same finite real shift from both sides preserves
`≤` for `EReal`. -/
-- Proof sketch: apply the `AddLECancellable` instance attached to adding a real scalar in
-- `EReal`.
private theorem add_coe_real_le_add_coe_real_iff (a b : EReal) (c : ℝ) :
    a + (c : EReal) ≤ b + (c : EReal) ↔ a ≤ b := by
  -- This is exactly the right-cancellation lemma for finite real shifts.
  exact (EReal.addLECancellable_coe c).add_le_add_iff_right

/-- Helper for Remark 9.37: canceling the same finite real shift from both sides preserves
`<` for `EReal`. -/
-- Proof sketch: rewrite strict inequality as negated `≤`, then apply the weak cancellation lemma.
private theorem add_coe_real_lt_add_coe_real_iff (a b : EReal) (c : ℝ) :
    a + (c : EReal) < b + (c : EReal) ↔ a < b := by
  -- Strict comparison is equivalent to the failure of the reversed weak comparison.
  rw [lt_iff_not_ge, lt_iff_not_ge, add_coe_real_le_add_coe_real_iff]

/-- Helper for Remark 9.37: a finite sum of real-cast values in `EReal` is the cast of the
corresponding real sum. -/
-- Proof sketch: induct over the finite set and combine the distinguished term with the induction
-- hypothesis using `EReal.coe_add`.
private theorem finset_sum_coe_real (s : Finset I) (r : I → ℝ) :
    (∑ i ∈ s, (r i : EReal)) = ((∑ i ∈ s, r i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, EReal.coe_add]

/-- Helper for Remark 9.37: coordinatewise convexity implies convexity of the finite direct sum on
its effective domain. -/
-- Proof sketch: apply each coordinate Jensen inequality to the corresponding coordinate of the
-- direct-sum convex combination, then sum the resulting inequalities over `Finset.univ`.
private theorem directSumFunction_convexOn_effectiveDomain_of_forall_convexOn
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hproper : ∀ i, IsProper (fun x : H i ↦ (f i x : EReal)))
    (hconv : ∀ i, ConvexOn (f i) (effectiveDomain (f i))) :
    ConvexOn (directSumFunction f) (effectiveDomain (directSumFunction f)) := by
  refine ⟨directSumFunction_effectiveDomain_nonempty_of_proper (f := f) hproper, ?_, ?_⟩
  · -- The chosen set is the effective domain itself.
    intro x hx
    exact hx
  · intro x hx y hy α hα0 hα1
    have hxcoord := (directSumFunction_mem_effectiveDomain_iff (f := f) (x := x)).1 hx
    have hycoord := (directSumFunction_mem_effectiveDomain_iff (f := f) (x := y)).1 hy
    let βE : EReal := ((1 - α : ℝ) : EReal)
    have hα_nonneg : 0 ≤ (α : EReal) := by
      exact_mod_cast hα0.le
    have hβ_nonneg : 0 ≤ βE := by
      change 0 ≤ (((1 - α : ℝ) : EReal))
      exact_mod_cast (sub_nonneg.mpr hα1.le)
    have hα_ne_top : (α : EReal) ≠ ⊤ := by
      simp
    have hβ_ne_top : βE ≠ ⊤ := by
      have hβ_lt_top : βE < ⊤ := by
        simpa [βE] using (EReal.coe_lt_top (1 - α))
      exact ne_of_lt hβ_lt_top
    have hcoord :
        ∀ i,
          (f i ((α • x + (1 - α) • y) i) : EReal) ≤
            (α : EReal) * (f i (x i) : EReal) + βE * (f i (y i) : EReal) := by
      intro i
      -- Each coordinate satisfies Jensen's inequality on its own effective domain.
      simpa [βE, Pi.add_apply, Pi.smul_apply] using
        (hconv i).ineq (hxcoord i) (hycoord i) hα0 hα1
    -- Summing the coordinate inequalities yields the direct-sum inequality.
    calc
      (directSumFunction f (α • x + (1 - α) • y) : EReal)
          = ∑ i, (f i ((α • x + (1 - α) • y) i) : EReal) := by
              rw [directSumFunction_apply]
      _ ≤ ∑ i, ((α : EReal) * (f i (x i) : EReal) + βE * (f i (y i) : EReal)) := by
            exact Finset.sum_le_sum (fun i _ ↦ hcoord i)
      _ = ∑ i, (α : EReal) * (f i (x i) : EReal) + ∑ i, βE * (f i (y i) : EReal) := by
            rw [Finset.sum_add_distrib]
      _ = (α : EReal) * ∑ i, (f i (x i) : EReal) + βE * ∑ i, (f i (y i) : EReal) := by
            rw [← ereal_mul_finset_sum_of_nonneg_of_ne_top
                (a := (α : EReal)) hα_nonneg hα_ne_top (s := Finset.univ)
                (b := fun i ↦ (f i (x i) : EReal)),
              ← ereal_mul_finset_sum_of_nonneg_of_ne_top
                (a := βE) hβ_nonneg hβ_ne_top (s := Finset.univ)
                (b := fun i ↦ (f i (y i) : EReal))]
      _ = (α : EReal) * (directSumFunction f x : EReal) +
            βE * (directSumFunction f y : EReal) := by
            rw [directSumFunction_apply, directSumFunction_apply]

/-- Helper for Remark 9.37: convexity of the finite direct sum transfers to each coordinate
function by freezing the remaining coordinates at a proper base point. -/
-- Proof sketch: evaluate the global Jensen inequality on coordinate slices, rewrite each sliced
-- direct-sum value as `active coordinate + constant tail`, then cancel the common finite tail.
private theorem forall_convexOn_of_directSumFunction_convexOn
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hproper : ∀ i, IsProper (fun x : H i ↦ (f i x : EReal)))
    (hconv : ConvexOn (directSumFunction f) (effectiveDomain (directSumFunction f))) :
    ∀ i, ConvexOn (f i) (effectiveDomain (f i)) := by
  classical
  let x₀ : ∀ i, H i := fun i ↦ Classical.choose (hproper i).2
  have hx₀ : ∀ i, x₀ i ∈ effectiveDomain (f i) := by
    intro i
    simpa [dom, effectiveDomain] using (Classical.choose_spec (hproper i).2)
  intro i
  refine ⟨⟨x₀ i, hx₀ i⟩, ?_, ?_⟩
  · -- The target set is again the effective domain itself.
    intro x hx
    exact hx
  · intro x hx y hy α hα0 hα1
    let βE : EReal := ((1 - α : ℝ) : EReal)
    let c : ℝ := ∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal
    have hα_nonneg : 0 ≤ (α : EReal) := by
      exact_mod_cast hα0.le
    have hβ_nonneg : 0 ≤ βE := by
      change 0 ≤ (((1 - α : ℝ) : EReal))
      exact_mod_cast (sub_nonneg.mpr hα1.le)
    have hα_ne_top : (α : EReal) ≠ ⊤ := by
      simp
    have hβ_ne_top : βE ≠ ⊤ := by
      have hβ_lt_top : βE < ⊤ := by
        simpa [βE] using (EReal.coe_lt_top (1 - α))
      exact ne_of_lt hβ_lt_top
    have hxs : coordinateSlice x₀ i x ∈ effectiveDomain (directSumFunction f) := by
      rw [directSumFunction_mem_effectiveDomain_iff]
      intro j
      by_cases hj : j = i
      · subst hj
        simpa [coordinateSlice]
      · simpa [coordinateSlice, Function.update, hj] using hx₀ j
    have hys : coordinateSlice x₀ i y ∈ effectiveDomain (directSumFunction f) := by
      rw [directSumFunction_mem_effectiveDomain_iff]
      intro j
      by_cases hj : j = i
      · subst hj
        simpa [coordinateSlice]
      · simpa [coordinateSlice, Function.update, hj] using hx₀ j
    have hslice :
        (f i (α • x + (1 - α) • y) : EReal) + (c : EReal) ≤
          (α : EReal) * ((f i x : EReal) + (c : EReal)) +
            βE * ((f i y : EReal) + (c : EReal)) := by
      have hglobal := hconv.ineq hxs hys hα0 hα1
      -- Rewrite the global inequality on slices into the active-coordinate plus frozen-tail form.
      rw [coordinateSlice_convexCombination,
        directSumFunction_coordinate_slice_apply (f := f) (x₀ := x₀) (hx₀ := hx₀) (i := i)
          (z := α • x + (1 - α) • y),
        directSumFunction_coordinate_slice_apply (f := f) (x₀ := x₀) (hx₀ := hx₀) (i := i)
          (z := x),
        directSumFunction_coordinate_slice_apply (f := f) (x₀ := x₀) (hx₀ := hx₀) (i := i)
          (z := y)] at hglobal
      simpa [βE, c] using hglobal
    have hrhs :
        (α : EReal) * ((f i x : EReal) + (c : EReal)) +
            βE * ((f i y : EReal) + (c : EReal)) =
          ((α : EReal) * (f i x : EReal) + βE * (f i y : EReal)) + (c : EReal) := by
      have hsum : (α : EReal) + βE = 1 := by
        change (((α + (1 - α : ℝ)) : EReal) = (1 : EReal))
        exact_mod_cast (show α + (1 - α : ℝ) = 1 by ring)
      -- Expand both weighted slice values and collect the common tail contribution.
      calc
        (α : EReal) * ((f i x : EReal) + (c : EReal)) +
            βE * ((f i y : EReal) + (c : EReal))
            = (((α : EReal) * (f i x : EReal) + (α : EReal) * (c : EReal)) +
                (βE * (f i y : EReal) + βE * (c : EReal))) := by
                  rw [EReal.left_distrib_of_nonneg_of_ne_top hα_nonneg hα_ne_top,
                    EReal.left_distrib_of_nonneg_of_ne_top hβ_nonneg hβ_ne_top]
        _ = ((α : EReal) * (f i x : EReal) + βE * (f i y : EReal)) +
              ((α : EReal) * (c : EReal) + βE * (c : EReal)) := by
              simp [add_assoc, add_left_comm, add_comm]
        _ = ((α : EReal) * (f i x : EReal) + βE * (f i y : EReal)) +
              (((α : EReal) + βE) * (c : EReal)) := by
              rw [← EReal.right_distrib_of_nonneg hα_nonneg hβ_nonneg]
        _ = ((α : EReal) * (f i x : EReal) + βE * (f i y : EReal)) + (c : EReal) := by
              rw [hsum, one_mul]
    have hcancel :
        (f i (α • x + (1 - α) • y) : EReal) ≤
          (α : EReal) * (f i x : EReal) + βE * (f i y : EReal) := by
      -- Cancel the same finite tail from the two sliced Jensen expressions.
      rw [hrhs] at hslice
      exact (add_coe_real_le_add_coe_real_iff _ _ c).1 hslice
    simpa [βE] using hcancel

/-- Helper for Remark 9.37: strict convexity of each coordinate function yields strict convexity
of the finite direct sum. -/
-- Proof sketch: choose one coordinate where two Hilbert-sum points differ, use the strict Jensen
-- inequality there and weak Jensen inequalities on the remaining coordinates, then sum them.
private theorem directSumFunction_strictlyConvex_of_forall_strictlyConvex
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hproper : ∀ i, IsProper (fun x : H i ↦ (f i x : EReal)))
    (hstrict : ∀ i, StrictlyConvex (f i)) :
    StrictlyConvex (directSumFunction f) := by
  intro x hx y hy hxy α hα0 hα1
  have hxcoord := (directSumFunction_mem_effectiveDomain_iff (f := f) (x := x)).1 hx
  have hycoord := (directSumFunction_mem_effectiveDomain_iff (f := f) (x := y)).1 hy
  classical
  have hcoord_ne : ∃ i, x i ≠ y i := by
    by_contra hnone
    apply hxy
    ext j
    by_contra hj
    exact hnone ⟨j, hj⟩
  rcases hcoord_ne with ⟨i, hi⟩
  let βE : EReal := ((1 - α : ℝ) : EReal)
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0.le
  have hβ_nonneg : 0 ≤ βE := by
    change 0 ≤ (((1 - α : ℝ) : EReal))
    exact_mod_cast (sub_nonneg.mpr hα1.le)
  have hα_ne_top : (α : EReal) ≠ ⊤ := by
    simp
  have hβ_ne_top : βE ≠ ⊤ := by
    have hβ_lt_top : βE < ⊤ := by
      simpa [βE] using (EReal.coe_lt_top (1 - α))
    exact ne_of_lt hβ_lt_top
  have hcoord_le :
      ∀ j,
        (f j ((α • x + (1 - α) • y) j) : EReal) ≤
          (α : EReal) * (f j (x j) : EReal) + βE * (f j (y j) : EReal) := by
    intro j
    -- The nondistinguished coordinates only require the weak Jensen inequality.
    simpa [βE, Pi.add_apply, Pi.smul_apply] using
      (convexOn_effectiveDomain_of_strictlyConvex (g := f j) (hproper := hproper j)
        (hg := hstrict j)).ineq (hxcoord j) (hycoord j) hα0 hα1
  have hcoord_lt :
      (f i ((α • x + (1 - α) • y) i) : EReal) <
        (α : EReal) * (f i (x i) : EReal) + βE * (f i (y i) : EReal) := by
    -- The distinguished coordinate contributes the strict Jensen inequality.
    simpa [βE, Pi.add_apply, Pi.smul_apply] using
      (hstrict i).ineq (hxcoord i) (hycoord i) hi hα0 hα1
  let L : I → ℝ := fun j ↦ (f j ((α • x + (1 - α) • y) j) : EReal).toReal
  let R : I → ℝ := fun j ↦
    α * (f j (x j) : EReal).toReal + (1 - α) * (f j (y j) : EReal).toReal
  have hright_eq : ∀ j,
      (α : EReal) * (f j (x j) : EReal) + βE * (f j (y j) : EReal) = (R j : EReal) := by
    intro j
    have hfx_top : (f j (x j) : EReal) ≠ ⊤ := ne_of_lt (hxcoord j)
    have hfy_top : (f j (y j) : EReal) ≠ ⊤ := ne_of_lt (hycoord j)
    have hfx_bot : (f j (x j) : EReal) ≠ ⊥ := ne_of_gt (f j (x j)).2
    have hfy_bot : (f j (y j) : EReal) ≠ ⊥ := ne_of_gt (f j (y j)).2
    -- Each weighted coordinate upper bound is a genuine real cast.
    calc
      (α : EReal) * (f j (x j) : EReal) + βE * (f j (y j) : EReal)
          = (α : EReal) * (((f j (x j) : EReal).toReal : ℝ) : EReal) +
              (((1 - α : ℝ) : EReal) * (((f j (y j) : EReal).toReal : ℝ) : EReal)) := by
                rw [show βE = (((1 - α : ℝ) : EReal)) by rfl,
                  EReal.coe_toReal hfx_top hfx_bot, EReal.coe_toReal hfy_top hfy_bot]
      _ = ((α * (f j (x j) : EReal).toReal + (1 - α) * (f j (y j) : EReal).toReal : ℝ) :
            EReal) := by
              rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      _ = (R j : EReal) := by
            simp [R]
  have hright_top : ∀ j,
      (α : EReal) * (f j (x j) : EReal) + βE * (f j (y j) : EReal) < ⊤ := by
    intro j
    rw [hright_eq j]
    exact EReal.coe_lt_top (R j)
  have hleft_eq : ∀ j, (f j ((α • x + (1 - α) • y) j) : EReal) = (L j : EReal) := by
    intro j
    -- The left coordinate is finite because it is bounded above by a finite right-hand side.
    symm
    exact EReal.coe_toReal (ne_of_lt (lt_of_le_of_lt (hcoord_le j) (hright_top j)))
      (ne_of_gt (f j ((α • x + (1 - α) • y) j)).2)
  have hcoord_le_real : ∀ j, L j ≤ R j := by
    intro j
    have hle := hcoord_le j
    rw [hleft_eq j, hright_eq j] at hle
    exact EReal.coe_le_coe_iff.mp hle
  have hcoord_lt_real : L i < R i := by
    have hlt := hcoord_lt
    rw [hleft_eq i, hright_eq i] at hlt
    exact EReal.coe_lt_coe_iff.mp hlt
  have hsum_lt :
      ∑ j, (f j ((α • x + (1 - α) • y) j) : EReal) <
        ∑ j, ((α : EReal) * (f j (x j) : EReal) + βE * (f j (y j) : EReal)) := by
    have hreal_sum_lt : ∑ j, L j < ∑ j, R j := by
      -- Over the reals, one strict coordinate inequality and weak inequalities elsewhere sum strictly.
      exact Finset.sum_lt_sum (fun j _ ↦ hcoord_le_real j) ⟨i, Finset.mem_univ i, hcoord_lt_real⟩
    have hsum_left_eq :
        ∑ j, (f j ((α • x + (1 - α) • y) j) : EReal) = ((∑ j, L j : ℝ) : EReal) := by
      calc
        ∑ j, (f j ((α • x + (1 - α) • y) j) : EReal) = ∑ j, (L j : EReal) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hleft_eq j
        _ = ((∑ j, L j : ℝ) : EReal) := by
          simpa using (finset_sum_coe_real (s := Finset.univ) (r := L))
    have hsum_right_eq :
        ∑ j, ((α : EReal) * (f j (x j) : EReal) + βE * (f j (y j) : EReal)) =
          ((∑ j, R j : ℝ) : EReal) := by
      calc
        ∑ j, ((α : EReal) * (f j (x j) : EReal) + βE * (f j (y j) : EReal)) = ∑ j, (R j : EReal) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hright_eq j
        _ = ((∑ j, R j : ℝ) : EReal) := by
          simpa using (finset_sum_coe_real (s := Finset.univ) (r := R))
    rw [hsum_left_eq, hsum_right_eq]
    exact EReal.coe_lt_coe_iff.mpr hreal_sum_lt
  calc
    (directSumFunction f (α • x + (1 - α) • y) : EReal)
        = ∑ j, (f j ((α • x + (1 - α) • y) j) : EReal) := by
            rw [directSumFunction_apply]
    _ < ∑ j, ((α : EReal) * (f j (x j) : EReal) + βE * (f j (y j) : EReal)) := hsum_lt
    _ = ∑ j, (α : EReal) * (f j (x j) : EReal) + ∑ j, βE * (f j (y j) : EReal) := by
          rw [Finset.sum_add_distrib]
    _ = (α : EReal) * ∑ j, (f j (x j) : EReal) + βE * ∑ j, (f j (y j) : EReal) := by
          rw [← ereal_mul_finset_sum_of_nonneg_of_ne_top
              (a := (α : EReal)) hα_nonneg hα_ne_top (s := Finset.univ)
              (b := fun j ↦ (f j (x j) : EReal)),
            ← ereal_mul_finset_sum_of_nonneg_of_ne_top
              (a := βE) hβ_nonneg hβ_ne_top (s := Finset.univ)
              (b := fun j ↦ (f j (y j) : EReal))]
    _ = (α : EReal) * (directSumFunction f x : EReal) +
          βE * (directSumFunction f y : EReal) := by
          rw [directSumFunction_apply, directSumFunction_apply]

/-- Helper for Remark 9.37: strict convexity of the finite direct sum transfers to each coordinate
function by restricting to coordinate slices. -/
-- Proof sketch: apply the global strict Jensen inequality to two slices through the same base
-- family, rewrite both direct-sum values as `active coordinate + constant tail`, and cancel.
private theorem forall_strictlyConvex_of_directSumFunction_strictlyConvex
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hproper : ∀ i, IsProper (fun x : H i ↦ (f i x : EReal)))
    (hstrict : StrictlyConvex (directSumFunction f)) :
    ∀ i, StrictlyConvex (f i) := by
  classical
  let x₀ : ∀ i, H i := fun i ↦ Classical.choose (hproper i).2
  have hx₀ : ∀ i, x₀ i ∈ effectiveDomain (f i) := by
    intro i
    simpa [dom, effectiveDomain] using (Classical.choose_spec (hproper i).2)
  intro i x hx y hy hxy α hα0 hα1
  let βE : EReal := ((1 - α : ℝ) : EReal)
  let c : ℝ := ∑ j ∈ Finset.univ.erase i, (f j (x₀ j) : EReal).toReal
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0.le
  have hβ_nonneg : 0 ≤ βE := by
    change 0 ≤ (((1 - α : ℝ) : EReal))
    exact_mod_cast (sub_nonneg.mpr hα1.le)
  have hα_ne_top : (α : EReal) ≠ ⊤ := by
    simp
  have hβ_ne_top : βE ≠ ⊤ := by
    have hβ_lt_top : βE < ⊤ := by
      simpa [βE] using (EReal.coe_lt_top (1 - α))
    exact ne_of_lt hβ_lt_top
  have hxs : coordinateSlice x₀ i x ∈ effectiveDomain (directSumFunction f) := by
    rw [directSumFunction_mem_effectiveDomain_iff]
    intro j
    by_cases hj : j = i
    · subst hj
      simpa [coordinateSlice]
    · simpa [coordinateSlice, Function.update, hj] using hx₀ j
  have hys : coordinateSlice x₀ i y ∈ effectiveDomain (directSumFunction f) := by
    rw [directSumFunction_mem_effectiveDomain_iff]
    intro j
    by_cases hj : j = i
    · subst hj
      simpa [coordinateSlice]
    · simpa [coordinateSlice, Function.update, hj] using hx₀ j
  have hslice_ne : coordinateSlice x₀ i x ≠ coordinateSlice x₀ i y := by
    intro hxy_slice
    apply hxy
    have hcoord := congrArg (fun z : lp H 2 ↦ z i) hxy_slice
    simpa [coordinateSlice] using hcoord
  have hslice :
      (f i (α • x + (1 - α) • y) : EReal) + (c : EReal) <
        (α : EReal) * ((f i x : EReal) + (c : EReal)) +
          βE * ((f i y : EReal) + (c : EReal)) := by
    have hglobal := hstrict.ineq hxs hys hslice_ne hα0 hα1
    -- Rewrite the global strict inequality on slices into the active-coordinate plus common-tail form.
    rw [coordinateSlice_convexCombination,
      directSumFunction_coordinate_slice_apply (f := f) (x₀ := x₀) (hx₀ := hx₀) (i := i)
        (z := α • x + (1 - α) • y),
      directSumFunction_coordinate_slice_apply (f := f) (x₀ := x₀) (hx₀ := hx₀) (i := i)
        (z := x),
      directSumFunction_coordinate_slice_apply (f := f) (x₀ := x₀) (hx₀ := hx₀) (i := i)
        (z := y)] at hglobal
    simpa [βE, c] using hglobal
  have hrhs :
      (α : EReal) * ((f i x : EReal) + (c : EReal)) +
          βE * ((f i y : EReal) + (c : EReal)) =
        ((α : EReal) * (f i x : EReal) + βE * (f i y : EReal)) + (c : EReal) := by
    have hsum : (α : EReal) + βE = 1 := by
      change (((α + (1 - α : ℝ)) : EReal) = (1 : EReal))
      exact_mod_cast (show α + (1 - α : ℝ) = 1 by ring)
    -- Expand both weighted slice values and collect the common tail contribution.
    calc
      (α : EReal) * ((f i x : EReal) + (c : EReal)) +
          βE * ((f i y : EReal) + (c : EReal))
          = (((α : EReal) * (f i x : EReal) + (α : EReal) * (c : EReal)) +
              (βE * (f i y : EReal) + βE * (c : EReal))) := by
                rw [EReal.left_distrib_of_nonneg_of_ne_top hα_nonneg hα_ne_top,
                  EReal.left_distrib_of_nonneg_of_ne_top hβ_nonneg hβ_ne_top]
      _ = ((α : EReal) * (f i x : EReal) + βE * (f i y : EReal)) +
            ((α : EReal) * (c : EReal) + βE * (c : EReal)) := by
            simp [add_assoc, add_left_comm, add_comm]
      _ = ((α : EReal) * (f i x : EReal) + βE * (f i y : EReal)) +
            (((α : EReal) + βE) * (c : EReal)) := by
            rw [← EReal.right_distrib_of_nonneg hα_nonneg hβ_nonneg]
      _ = ((α : EReal) * (f i x : EReal) + βE * (f i y : EReal)) + (c : EReal) := by
            rw [hsum, one_mul]
  have hcancel :
      (f i (α • x + (1 - α) • y) : EReal) <
        (α : EReal) * (f i x : EReal) + βE * (f i y : EReal) := by
    -- Cancel the same finite tail from the strict slice inequality.
    rw [hrhs] at hslice
    exact (add_coe_real_lt_add_coe_real_iff _ _ c).1 hslice
  simpa [βE] using hcancel

/-- Remark 9.37: for a finite family of proper functions on real Hilbert spaces, the direct-sum
function on the Hilbert direct sum is convex on its effective domain exactly when each coordinate
function is convex on its own effective domain, and it is strictly convex exactly when each
coordinate function is strictly convex. -/
-- Proof sketch: for convexity, combine Proposition 8.6 with the epigraph/Jensen characterization
-- from Proposition 8.4 applied coordinatewise. For strict convexity, freeze all coordinates except
-- one at proper base points supplied by `hproper`, then reduce the direct-sum Jensen inequality to
-- the corresponding coordinate inequality and conversely sum the coordinate inequalities.
theorem directSumFunction_convexOn_effectiveDomain_and_strictlyConvex_iff
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hproper : ∀ i, IsProper (fun x : H i ↦ (f i x : EReal))) :
    (ConvexOn (directSumFunction f) (effectiveDomain (directSumFunction f)) ↔
      ∀ i, ConvexOn (f i) (effectiveDomain (f i))) ∧
    (StrictlyConvex (directSumFunction f) ↔ ∀ i, StrictlyConvex (f i)) := by
  constructor
  · constructor
    · intro hconv
      -- Freeze the other coordinates to read the global Jensen inequality on each coordinate slice.
      exact forall_convexOn_of_directSumFunction_convexOn (f := f) hproper hconv
    · intro hconv
      -- Sum the coordinatewise Jensen inequalities to recover convexity of the direct sum.
      exact directSumFunction_convexOn_effectiveDomain_of_forall_convexOn
        (f := f) hproper hconv
  · constructor
    · intro hstrict
      -- The strict Jensen inequality on the direct sum restricts to strict inequalities on slices.
      exact forall_strictlyConvex_of_directSumFunction_strictlyConvex
        (f := f) hproper hstrict
    · intro hstrict
      -- One strict coordinate inequality plus weak inequalities elsewhere gives strictness globally.
      exact directSumFunction_strictlyConvex_of_forall_strictlyConvex
        (f := f) hproper hstrict

/-- If each coordinate function belongs to `Γ₀`, then their finite direct sum again belongs to
`Γ₀` on the Hilbert direct sum. -/
-- Proof sketch: lower semicontinuity is preserved by the finite sum of the coordinate functions,
-- and the convexity component is exactly the forward implication of
-- `directSumFunction_convexOn_effectiveDomain_and_strictlyConvex_iff`.
theorem directSumFunction_mem_gammaZero_of_forall_mem_gammaZero
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hf : ∀ i, f i ∈ Γ₀(H i)) :
    directSumFunction f ∈ Γ₀(lp H 2) := by
  rw [mem_gammaZero_iff]
  constructor
  · have hlsc : ∀ i, LowerSemicontinuous (fun x : H i ↦ (f i x : EReal)) := by
      intro i
      exact (mem_gammaZero_iff.mp (hf i)).1
    -- Lower semicontinuity is preserved by summing the coordinate functions over the finite index set.
    exact directSumFunction_lowerSemicontinuous (f := f) hlsc
  · have hproper : ∀ i, IsProper (fun x : H i ↦ (f i x : EReal)) := by
      intro i
      exact isProper_of_mem_gammaZero (hf i)
    have hconv : ∀ i, ConvexOn (f i) (effectiveDomain (f i)) := by
      intro i
      exact (mem_gammaZero_iff.mp (hf i)).2
    -- The forward convexity half of Remark 9.37 is exactly the needed `Γ₀` stability statement.
    exact directSumFunction_convexOn_effectiveDomain_of_forall_convexOn
      (f := f) hproper hconv

end Hilbert

end ERealFunction
