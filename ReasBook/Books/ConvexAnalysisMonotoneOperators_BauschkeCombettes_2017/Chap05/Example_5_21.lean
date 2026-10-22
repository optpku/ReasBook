/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Remark_4_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_42
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_47
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Corollary_4_51
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_16

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Topology

universe u v

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type v}

local notation "H_univ" => (Set.univ : Set H)

-- Proof sketch: a point in the common intersection belongs to every component set, so it gives a
-- witness of nonemptiness for each `C j`.
/-- A nonempty common intersection makes every component set nonempty. -/
private theorem nonempty_component_of_nonempty_iInter (C : I → Set H)
    (hC_inter_nonempty : (⋂ j, C j).Nonempty) (j : I) :
    (C j).Nonempty := by
  -- A witness in the common intersection lies in the `j`-th component.
  rcases hC_inter_nonempty with ⟨x, hx⟩
  exact ⟨x, Set.mem_iInter.mp hx j⟩

/-- Helper for Example 5.21: points already in a nonempty closed convex set are fixed by its
metric projection. -/
private theorem projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {x : H}
    (hx : x ∈ C) :
    projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x =
      x := by
  have hxproj :
      x =
        projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mpr <| by
          refine ⟨hx, ?_⟩
          intro y hy
          simp
  simpa using hxproj.symm

/-- Helper for Example 5.21: the fixed points of the metric projection onto a nonempty closed
convex set are exactly that set. -/
private theorem fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    Function.fixedPoints
        (projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)) =
      C := by
  ext x
  constructor
  · intro hx
    rw [Function.mem_fixedPoints_iff] at hx
    -- Projection points always lie in the target set.
    simpa [hx] using
      projectionPoint_mem C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  · intro hx
    rw [Function.mem_fixedPoints_iff]
    -- A point already in `C` is its own projection.
    exact
      projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex hx

/-- Helper for Example 5.21: a firmly nonexpansive self-map in the residual sense is
`1 / 2`-averaged. -/
private theorem averagedWith_half_of_isFirmlyNonexpansiveOn {D : Set H} {T : D → H}
    (hT : IsFirmlyNonexpansiveOn T) :
    AveragedWith (1 / 2 : ℝ) T := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    norm_num
  rw [averagedWith_iff_residual_sqnorm_ineq hhalf]
  intro x y
  have hxy := hT x y
  norm_num
  simpa using hxy

/-- The relaxed projector family `Tᵢ = (1 - βᵢ) Id + βᵢ P_{Cᵢ}` attached to a family of nonempty
closed convex sets with nonempty common intersection. -/
noncomputable def relaxedProjectionFamily (C : I → Set H) (hC_closed : ∀ j, IsClosed (C j))
    (hC_convex : ∀ j, Convex ℝ (C j)) (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ) :
    I → H → H :=
  fun j x ↦
    (1 - β j) • x + β j •
      projectionPoint (C j)
        (isChebyshev_of_nonempty_isClosed_convex
          (nonempty_component_of_nonempty_iInter C hC_inter_nonempty j)
          (hC_closed j) (hC_convex j)) x

-- Proof sketch: unfold `relaxedProjectionFamily`.
/-- Evaluating the relaxed projector family gives the textbook formula
`Tᵢ x = (1 - βᵢ) x + βᵢ P_{Cᵢ} x`. -/
@[simp] theorem relaxedProjectionFamily_apply (C : I → Set H) (hC_closed : ∀ j, IsClosed (C j))
    (hC_convex : ∀ j, Convex ℝ (C j)) (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ)
    (j : I) (x : H) :
    relaxedProjectionFamily C hC_closed hC_convex hC_inter_nonempty β j x =
      (1 - β j) • x + β j •
        projectionPoint (C j)
          (isChebyshev_of_nonempty_isClosed_convex
            (nonempty_component_of_nonempty_iInter C hC_inter_nonempty j)
            (hC_closed j) (hC_convex j)) x := by
  -- This is the defining equation of the relaxed projector family.
  rfl

/-- The `k`-th ordered block composition of the relaxed projector family. -/
noncomputable abbrev stringBlockCompositionOperator {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (C : I → Set H) (hC_closed : ∀ j, IsClosed (C j))
    (hC_convex : ∀ j, Convex ℝ (C j)) (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ)
    (k : Fin p) :
    H → H :=
  finiteComposition (fun l : Fin (m k) ↦
    relaxedProjectionFamily C hC_closed hC_convex hC_inter_nonempty β (i k l))

-- Proof sketch: unfold `stringBlockCompositionOperator`.
/-- The `k`-th string block operator is the ordered composition of the relaxed projectors indexed
by that block. -/
@[simp] theorem stringBlockCompositionOperator_eq_finiteComposition {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (C : I → Set H) (hC_closed : ∀ j, IsClosed (C j))
    (hC_convex : ∀ j, Convex ℝ (C j)) (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ)
    (k : Fin p) :
    stringBlockCompositionOperator m i C hC_closed hC_convex hC_inter_nonempty β k =
      finiteComposition (fun l : Fin (m k) ↦
        relaxedProjectionFamily C hC_closed hC_convex hC_inter_nonempty β (i k l)) := by
  -- The block operator is defined by this ordered composition.
  rfl

/-- The string-averaged relaxed projection operator given by the weighted average of the ordered
block compositions of the relaxed projectors. -/
noncomputable abbrev stringAveragedRelaxedProjectionOperator {p : ℕ+} (ω : Fin p → ℝ)
    (m : Fin p → ℕ+) (i : (k : Fin p) → Fin (m k) → I) (C : I → Set H)
    (hC_closed : ∀ j, IsClosed (C j)) (hC_convex : ∀ j, Convex ℝ (C j))
    (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ) :
    H → H :=
  fun x ↦
    ∑ k : Fin p, ω k •
      stringBlockCompositionOperator m i C hC_closed hC_convex hC_inter_nonempty β k x

-- Proof sketch: unfold `stringAveragedRelaxedProjectionOperator`.
/-- Evaluating the string-averaged relaxed projection operator gives the weighted sum of the block
compositions of the relaxed projector family. -/
@[simp] theorem stringAveragedRelaxedProjectionOperator_apply {p : ℕ+} (ω : Fin p → ℝ)
    (m : Fin p → ℕ+) (i : (k : Fin p) → Fin (m k) → I) (C : I → Set H)
    (hC_closed : ∀ j, IsClosed (C j)) (hC_convex : ∀ j, Convex ℝ (C j))
    (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ) (x : H) :
    stringAveragedRelaxedProjectionOperator ω m i C hC_closed hC_convex hC_inter_nonempty β x =
      ∑ k : Fin p,
        ω k •
          stringBlockCompositionOperator m i C hC_closed hC_convex hC_inter_nonempty β k x := by
  -- Evaluating the weighted average only unfolds the definition.
  rfl

/-- The orbit generated by iterating the string-averaged relaxed projection operator from `x₀`. -/
noncomputable def stringAveragedRelaxedProjectionOrbit {p : ℕ+} (ω : Fin p → ℝ)
    (m : Fin p → ℕ+) (i : (k : Fin p) → Fin (m k) → I) (C : I → Set H)
    (hC_closed : ∀ j, IsClosed (C j)) (hC_convex : ∀ j, Convex ℝ (C j))
    (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ) (x₀ : H) :
    ℕ → H :=
  fun n ↦ (stringAveragedRelaxedProjectionOperator ω m i C hC_closed hC_convex
    hC_inter_nonempty β)^[n] x₀

-- Proof sketch: unfold the orbit and use the standard successor identity for function iterates.
/-- The string-averaged relaxed projection orbit satisfies the recursion
`xₙ₊₁ = S xₙ`, where `S` is the associated string-averaged relaxed projection operator. -/
theorem stringAveragedRelaxedProjectionOrbit_succ {p : ℕ+} (ω : Fin p → ℝ) (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (C : I → Set H) (hC_closed : ∀ j, IsClosed (C j))
    (hC_convex : ∀ j, Convex ℝ (C j)) (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ)
    (x₀ : H) (n : ℕ) :
    stringAveragedRelaxedProjectionOrbit ω m i C hC_closed hC_convex hC_inter_nonempty β x₀
        (n + 1) =
      stringAveragedRelaxedProjectionOperator ω m i C hC_closed hC_convex hC_inter_nonempty β
        (stringAveragedRelaxedProjectionOrbit ω m i C hC_closed hC_convex hC_inter_nonempty β
          x₀ n) := by
  -- The orbit is defined by iterating the string-averaged operator.
  simp [stringAveragedRelaxedProjectionOrbit, Function.iterate_succ_apply']

/-- Helper for Example 5.21: the averaging parameter attached to a single ordered block. -/
private noncomputable def blockAveragingParameter {p : ℕ+}
    (m : Fin p → ℕ+) (i : (k : Fin p) → Fin (m k) → I)
    (avg : I → ℝ) (k : Fin p) : ℝ :=
  1 / (1 + (∑ l : Fin (m k), avg (i k l) / (1 - avg (i k l)))⁻¹)

/-- Helper for Example 5.21: the weighted average of the block averaging parameters. -/
private noncomputable def weightedBlockAveragingParameter {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (avg : I → ℝ) (ω : Fin p → ℝ) : ℝ :=
  ∑ k : Fin p, ω k * blockAveragingParameter m i avg k

/-- Helper for Example 5.21: the ordered composition attached to a single block for a family of
self-maps. -/
private noncomputable abbrev blockComposition {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H) (k : Fin p) : H → H :=
  finiteComposition (fun l : Fin (m k) ↦ T (i k l))

/-- Helper for Example 5.21: the weighted average of the ordered block compositions. -/
private noncomputable def weightedBlockOperator {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H) (ω : Fin p → ℝ) : H → H :=
  fun x ↦
    weightedOperatorAverage ω
      (fun k : Fin p ↦ fun y : H_univ ↦ blockComposition m i T k y)
      ⟨x, Set.mem_univ _⟩

/-- Helper for Example 5.21: a family of ambient self-maps lifts canonically to `Set.univ`. -/
private noncomputable def liftUnivFamily {m : ℕ} (T : Fin m → H → H) :
    Fin m → H_univ → H_univ :=
  fun j x ↦ ⟨T j (x : H), Set.mem_univ _⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 5.21: coercing a lifted map back to the ambient space recovers the original
self-map. -/
@[simp] private theorem liftUnivFamily_coe {m : ℕ} (T : Fin m → H → H) (j : Fin m)
    (x : H_univ) :
    ((liftUnivFamily T j x : H_univ) : H) = T j (x : H) :=
  rfl

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 5.21: lifting a finite ordered composition to `Set.univ` preserves its
ambient value after coercion. -/
@[simp] private theorem finiteComposition_liftUnivFamily_coe :
    {m : ℕ} → (T : Fin m → H → H) → ∀ x : H_univ,
      ((finiteComposition (liftUnivFamily T) x : H_univ) : H) = finiteComposition T (x : H)
  | 0, _, _ => rfl
  | _ + 1, T, x => by
      -- Expand the head-tail composition and rewrite the lifted tail recursively.
      rw [finiteComposition_succ, finiteComposition_succ]
      simp only [Function.comp_apply, liftUnivFamily_coe]
      exact congrArg (T 0) (finiteComposition_liftUnivFamily_coe (T := fun j ↦ T j.succ) (x := x))

/-- Helper for Example 5.21: a one-term block parameter simplifies to the original averaging
parameter. -/
private theorem inv_one_add_inv_eq_of_mem_Ioo {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    1 / (1 + (a / (1 - a))⁻¹) = a := by
  have ha0 : a ≠ 0 := ne_of_gt ha.1
  have h1a0 : 1 - a ≠ 0 := sub_ne_zero.mpr (ne_of_lt ha.2).symm
  have hone_sub_pos : 0 < 1 - a := sub_pos.mpr ha.2
  have hfrac_pos : 0 < a / (1 - a) := div_pos ha.1 hone_sub_pos
  have hsum0 : 1 + (a / (1 - a))⁻¹ ≠ 0 := by
    have hfrac_inv_pos : 0 < (a / (1 - a))⁻¹ := inv_pos.mpr hfrac_pos
    have : 0 < 1 + (a / (1 - a))⁻¹ := by
      linarith
    exact ne_of_gt this
  field_simp [ha0, h1a0, hsum0]
  ring

/-- Helper for Example 5.21: the averaging parameter of a singleton block is the averaging
parameter of its unique factor. -/
private theorem block_averaging_parameter_eq_of_card_one {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H) (avg : I → ℝ)
    (hT : ∀ j, AveragedWith (avg j) (fun x : H_univ ↦ T j x))
    (k : Fin p) (hm1 : (m k : ℕ) = 1) :
    blockAveragingParameter m i avg k = avg (i k 0) := by
  have hl0 : ∀ l : Fin (m k), l = 0 := by
    intro l
    apply Fin.ext
    omega
  have hi0 : ∀ l : Fin (m k), i k l = i k 0 := by
    intro l
    rw [hl0 l]
  -- Collapse the one-term beta-sum to the unique entry indexed by `0`.
  rw [blockAveragingParameter]
  simp_rw [hi0]
  simpa [hm1] using inv_one_add_inv_eq_of_mem_Ioo ((hT (i k 0)).mem_Ioo)

/-- Helper for Example 5.21: the ordered composition of a singleton family is the unique map in
that family. -/
private theorem finiteComposition_const_eq_of_card_one (f : H → H) {n : ℕ} (hn : n = 1) :
    finiteComposition (fun _ : Fin n ↦ f) = f := by
  cases hn
  funext x
  simp [finiteComposition, Function.comp_apply]

/-- Helper for Example 5.21: a singleton block composition is just its unique factor. -/
private theorem block_composition_eq_of_card_one {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H)
    (k : Fin p) (hm1 : (m k : ℕ) = 1) :
    blockComposition m i T k = T (i k 0) := by
  have hl0 : ∀ l : Fin (m k), l = 0 := by
    intro l
    apply Fin.ext
    omega
  have hblock :
      (fun l : Fin (m k) ↦ T (i k l)) = fun _ : Fin (m k) ↦ T (i k 0) := by
    funext l
    rw [hl0 l]
  -- Collapse the one-term ordered composition to the only available factor.
  rw [blockComposition, hblock]
  exact finiteComposition_const_eq_of_card_one (T (i k 0)) hm1

/-- Helper for Example 5.21: each ordered block composition is averaged with the textbook block
parameter. -/
private theorem block_composition_averaged_with {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H) (avg : I → ℝ)
    (hT : ∀ j, AveragedWith (avg j) (fun x : H_univ ↦ T j x)) (k : Fin p) :
    AveragedWith (blockAveragingParameter m i avg k)
      (fun x : H_univ ↦ blockComposition m i T k x) := by
  by_cases hm1 : (m k : ℕ) = 1
  · -- Route correction: treat singleton blocks separately instead of forcing Proposition 4.46
    -- through the degenerate one-term case.
    have hparam_eq :
        blockAveragingParameter m i avg k = avg (i k 0) :=
      block_averaging_parameter_eq_of_card_one m i T avg hT k hm1
    have hblock_eq : blockComposition m i T k = T (i k 0) :=
      block_composition_eq_of_card_one m i T k hm1
    rw [hparam_eq, hblock_eq]
    exact hT (i k 0)
  · have hm2 : 2 ≤ (m k : ℕ) := by
      have hmpos : 0 < (m k : ℕ) := (m k).pos
      omega
    have hcomp :
        AveragedWith (blockAveragingParameter m i avg k)
          (fun x : H_univ ↦
            ((finiteComposition (liftUnivFamily (fun l : Fin (m k) ↦ T (i k l))) x : H_univ) : H)) := by
      -- Proposition 4.46 applies directly to the lifted block family on `Set.univ`.
      simpa [blockAveragingParameter] using
        averagedWith_compose_fin (D := H_univ) hm2 ⟨0, Set.mem_univ _⟩
          (fun l : Fin (m k) ↦ avg (i k l))
          (liftUnivFamily (fun l : Fin (m k) ↦ T (i k l)))
          (fun l ↦ by simpa using hT (i k l))
    -- Coercing the lifted composition recovers the ambient block operator.
    simpa [blockComposition, finiteComposition_liftUnivFamily_coe] using hcomp

/-- Helper for Example 5.21: the fixed points of a block composition are exactly the common fixed
points of the operators in that block. -/
private theorem fixed_points_block_composition_eq_iInter {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H) (avg : I → ℝ)
    (hT : ∀ j, AveragedWith (avg j) (fun x : H_univ ↦ T j x))
    (hFix : (⋂ j, Function.fixedPoints (T j)).Nonempty) (k : Fin p) :
    Function.fixedPoints (blockComposition m i T k) =
      ⋂ l : Fin (m k), Function.fixedPoints (T (i k l)) := by
  let U : Fin (m k) → H_univ → H_univ := liftUnivFamily (fun l : Fin (m k) ↦ T (i k l))
  have hAveraged :
      ∀ l : Fin (m k), ∃ α, AveragedWith α (fun x : H_univ ↦ ((U l x : H_univ) : H)) := by
    intro l
    refine ⟨avg (i k l), ?_⟩
    simpa [U] using hT (i k l)
  have hfixU : Set.Nonempty (⋂ l : Fin (m k), Function.fixedPoints (U l) : Set H_univ) := by
    rcases hFix with ⟨z, hz⟩
    refine ⟨⟨z, Set.mem_univ _⟩, ?_⟩
    rw [Set.mem_iInter]
    intro l
    rw [Function.mem_fixedPoints_iff]
    apply Subtype.ext
    -- A common fixed point of the ambient family fixes each lifted block entry.
    have hzl : T (i k l) z = z := (Set.mem_iInter.mp hz) (i k l)
    simpa [U] using hzl
  have hfix_eq :
      Function.fixedPoints (finiteComposition U) = ⋂ l : Fin (m k), Function.fixedPoints (U l) :=
    fixedPoints_finiteComposition_eq_iInter_fixedPoints_of_averagedWith (T := U) hAveraged hfixU
  ext x
  constructor
  · intro hx
    have hx_univ : (⟨x, Set.mem_univ _⟩ : H_univ) ∈ Function.fixedPoints (finiteComposition U) := by
      rw [Function.mem_fixedPoints_iff] at hx ⊢
      apply Subtype.ext
      -- Reinterpret the ambient block fixed-point equation on the lifted family.
      simpa [U, blockComposition, finiteComposition_liftUnivFamily_coe] using hx
    have hx_iInter :
        (⟨x, Set.mem_univ _⟩ : H_univ) ∈ ⋂ l : Fin (m k), Function.fixedPoints (U l) := by
      simpa [hfix_eq] using hx_univ
    rw [Set.mem_iInter]
    intro l
    have hxl : (⟨x, Set.mem_univ _⟩ : H_univ) ∈ Function.fixedPoints (U l) :=
      (Set.mem_iInter.mp hx_iInter) l
    rw [Function.mem_fixedPoints_iff] at hxl ⊢
    -- Coercing the lifted fixed-point equation returns the ambient one.
    simpa [U] using congrArg Subtype.val hxl
  · intro hx
    have hx_iInter :
        (⟨x, Set.mem_univ _⟩ : H_univ) ∈ ⋂ l : Fin (m k), Function.fixedPoints (U l) := by
      rw [Set.mem_iInter]
      intro l
      rw [Function.mem_fixedPoints_iff]
      apply Subtype.ext
      -- Each ambient factor fixes `x`, so the lifted factor fixes `⟨x, _⟩`.
      have hxl : T (i k l) x = x := (Set.mem_iInter.mp hx) l
      simpa [U] using hxl
    have hx_univ : (⟨x, Set.mem_univ _⟩ : H_univ) ∈ Function.fixedPoints (finiteComposition U) := by
      simpa [hfix_eq] using hx_iInter
    rw [Function.mem_fixedPoints_iff] at hx_univ ⊢
    -- Coercing the lifted composition fixed-point equation recovers the ambient block equation.
    simpa [U, blockComposition, finiteComposition_liftUnivFamily_coe] using congrArg Subtype.val hx_univ

/-- Helper for Example 5.21: surjectivity of the block index map turns the nested blockwise
intersection back into the common intersection over the original family. -/
private theorem iInter_blocks_eq_iInter_of_surjective {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (A : I → Set H)
    (hcover : Function.Surjective (fun q : Σ k : Fin p, Fin (m k) ↦ i q.1 q.2)) :
    (⋂ k : Fin p, ⋂ l : Fin (m k), A (i k l)) = ⋂ j : I, A j := by
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro hx j
    rcases hcover j with ⟨q, rfl⟩
    exact hx q.1 q.2
  · intro hx k l
    exact hx (i k l)

/-- Helper for Example 5.21: the weighted block operator has exactly the common fixed points of
the original family. -/
private theorem fixed_points_weighted_block_operator_eq_iInter {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H) (avg : I → ℝ) (ω : Fin p → ℝ)
    (hT : ∀ j, AveragedWith (avg j) (fun x : H_univ ↦ T j x))
    (hFix : (⋂ j, Function.fixedPoints (T j)).Nonempty) (hω : ∀ k, ω k ∈ Set.Ioc (0 : ℝ) 1)
    (hω_sum : ∑ k : Fin p, ω k = 1)
    (hcover : Function.Surjective (fun q : Σ k : Fin p, Fin (m k) ↦ i q.1 q.2)) :
    Function.fixedPoints (weightedBlockOperator m i T ω) = ⋂ j : I, Function.fixedPoints (T j) := by
  have hBlockQuasi :
      ∀ k : Fin p, IsQuasinonexpansiveOn (fun x : H_univ ↦ blockComposition m i T k x) := by
    intro k
    exact averaged_quasinonexpansiveOn (block_composition_averaged_with m i T avg hT k)
  have hBlockFixNonempty :
      (⋂ k : Fin p, fixedPointsWithin (fun x : H_univ ↦ blockComposition m i T k x)).Nonempty := by
    rcases hFix with ⟨z, hz⟩
    refine ⟨⟨z, Set.mem_univ _⟩, ?_⟩
    rw [Set.mem_iInter]
    intro k
    rw [mem_fixedPointsWithin_iff]
    have hzk : z ∈ Function.fixedPoints (blockComposition m i T k) := by
      have hzBlock :
          z ∈ ⋂ l : Fin (m k), Function.fixedPoints (T (i k l)) := by
        rw [Set.mem_iInter]
        intro l
        exact (Set.mem_iInter.mp hz) (i k l)
      have hblock_eq :
          Function.fixedPoints (blockComposition m i T k) =
            ⋂ l : Fin (m k), Function.fixedPoints (T (i k l)) :=
        fixed_points_block_composition_eq_iInter m i T avg hT ⟨z, hz⟩ k
      rw [hblock_eq]
      exact hzBlock
    rw [Function.mem_fixedPoints_iff] at hzk
    simpa using hzk
  have hFixWithinEq :
      fixedPointsWithin
          (fun x : H_univ ↦
            weightedOperatorAverage ω
              (fun k : Fin p ↦ fun y : H_univ ↦ blockComposition m i T k y) x) =
        ⋂ k : Fin p, fixedPointsWithin (fun x : H_univ ↦ blockComposition m i T k x) :=
    fixedPointsWithin_weightedAverage_eq_iInter ω
      (fun k : Fin p ↦ fun x : H_univ ↦ blockComposition m i T k x) hBlockQuasi hBlockFixNonempty
      (fun k ↦ (hω k).1) hω_sum
  ext x
  constructor
  · intro hx
    have hxWithin :
        (⟨x, Set.mem_univ _⟩ : H_univ) ∈
          fixedPointsWithin
            (fun y : H_univ ↦
              weightedOperatorAverage ω
                (fun k : Fin p ↦ fun z : H_univ ↦ blockComposition m i T k z) y) := by
      rw [mem_fixedPointsWithin_iff]
      rw [Function.mem_fixedPoints_iff] at hx
      -- Reinterpret the ambient fixed-point equation as a fixed point on `Set.univ`.
      simpa [weightedBlockOperator] using hx
    have hxBlocksWithin :
        (⟨x, Set.mem_univ _⟩ : H_univ) ∈
          ⋂ k : Fin p, fixedPointsWithin (fun y : H_univ ↦ blockComposition m i T k y) := by
      rw [← hFixWithinEq]
      exact hxWithin
    have hxBlocks :
        x ∈ ⋂ k : Fin p, Function.fixedPoints (blockComposition m i T k) := by
      rw [Set.mem_iInter]
      intro k
      have hxk :
          (⟨x, Set.mem_univ _⟩ : H_univ) ∈
            fixedPointsWithin (fun y : H_univ ↦ blockComposition m i T k y) :=
        (Set.mem_iInter.mp hxBlocksWithin) k
      rw [mem_fixedPointsWithin_iff] at hxk
      rw [Function.mem_fixedPoints_iff]
      simpa using hxk
    have hxNested :
        x ∈ ⋂ k : Fin p, ⋂ l : Fin (m k), Function.fixedPoints (T (i k l)) := by
      rw [Set.mem_iInter]
      intro k
      have hblock_eq :
          Function.fixedPoints (blockComposition m i T k) =
            ⋂ l : Fin (m k), Function.fixedPoints (T (i k l)) :=
        fixed_points_block_composition_eq_iInter m i T avg hT hFix k
      rw [← hblock_eq]
      exact (Set.mem_iInter.mp hxBlocks) k
    -- Surjectivity of the block index map turns the nested block intersection back into the
    -- common fixed-point set of the original family.
    simpa [iInter_blocks_eq_iInter_of_surjective m i (fun j ↦ Function.fixedPoints (T j)) hcover]
      using hxNested
  · intro hx
    have hxNested :
        x ∈ ⋂ k : Fin p, ⋂ l : Fin (m k), Function.fixedPoints (T (i k l)) := by
      rw [Set.mem_iInter]
      intro k
      rw [Set.mem_iInter]
      intro l
      exact (Set.mem_iInter.mp hx) (i k l)
    have hxBlocks :
        x ∈ ⋂ k : Fin p, Function.fixedPoints (blockComposition m i T k) := by
      rw [Set.mem_iInter]
      intro k
      have hblock_eq :
          Function.fixedPoints (blockComposition m i T k) =
            ⋂ l : Fin (m k), Function.fixedPoints (T (i k l)) :=
        fixed_points_block_composition_eq_iInter m i T avg hT hFix k
      rw [hblock_eq]
      exact (Set.mem_iInter.mp hxNested) k
    have hxBlocksWithin :
        (⟨x, Set.mem_univ _⟩ : H_univ) ∈
          ⋂ k : Fin p, fixedPointsWithin (fun y : H_univ ↦ blockComposition m i T k y) := by
      rw [Set.mem_iInter]
      intro k
      rw [mem_fixedPointsWithin_iff]
      have hxk : x ∈ Function.fixedPoints (blockComposition m i T k) := (Set.mem_iInter.mp hxBlocks) k
      rw [Function.mem_fixedPoints_iff] at hxk
      simpa using hxk
    have hxWithin :
        (⟨x, Set.mem_univ _⟩ : H_univ) ∈
          fixedPointsWithin
            (fun y : H_univ ↦
              weightedOperatorAverage ω
                (fun k : Fin p ↦ fun z : H_univ ↦ blockComposition m i T k z) y) := by
      rw [hFixWithinEq]
      exact hxBlocksWithin
    rw [mem_fixedPointsWithin_iff] at hxWithin
    rw [Function.mem_fixedPoints_iff]
    -- Coercing the subtype fixed-point equation returns the ambient weighted block equation.
    simpa [weightedBlockOperator] using hxWithin

-- Proof sketch: identify each block composition as averaged with the textbook parameter, pass to
-- their weighted average, identify the corresponding fixed-point set with the common fixed points
-- of the original family, and then invoke Proposition 5.16 for the relaxed iteration of that
-- single weighted block operator.
/-- Helper for Example 5.21: the Corollary 5.19 convergence mechanism for weighted block
compositions of averaged operators. -/
private theorem exists_tendsto_weakly_to_common_fixedPoint_of_krasnoselskiiMann_weightedBlockComposition
    {p : ℕ+} (m : Fin p → ℕ+) (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H)
    (avg : I → ℝ) (ω : Fin p → ℝ)
    (hT : ∀ j, AveragedWith (avg j) (fun x : H_univ ↦ T j x))
    (hFix : (⋂ j, Function.fixedPoints (T j)).Nonempty)
    (hω : ∀ k, ω k ∈ Set.Ioc (0 : ℝ) 1) (hω_sum : ∑ k : Fin p, ω k = 1)
    (hcover : Function.Surjective (fun q : Σ k : Fin p, Fin (m k) ↦ i q.1 q.2))
    (lam : ℕ → ℝ)
    (hlam : ∀ n,
      lam n ∈ Set.Icc (0 : ℝ)
        (1 /
          ∑ k : Fin p,
            ω k *
              (1 /
                (1 + (∑ l : Fin (m k), avg (i k l) / (1 - avg (i k l)))⁻¹))))
    (hdiv :
      Tendsto
        (fun N ↦ ∑ n ∈ Finset.range N,
          lam n *
            (1 -
              (∑ k : Fin p,
                  ω k *
                    (1 /
                      (1 + (∑ l : Fin (m k), avg (i k l) / (1 - avg (i k l)))⁻¹))) *
                lam n))
        atTop atTop)
    (x₀ : H) :
    let S : H → H :=
      fun x ↦
        weightedOperatorAverage ω
          (fun k : Fin p ↦
            fun y : H_univ ↦
              finiteComposition (fun l : Fin (m k) ↦ T (i k l)) y)
          ⟨x, by simp⟩
    ∃ z ∈ ⋂ j, Function.fixedPoints (T j),
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (relaxedOperatorIteration (fun _ ↦ S) lam x₀ n))
        atTop (𝓝 (toWeakSpace ℝ H z)) := by
  dsimp
  let α : ℝ := weightedBlockAveragingParameter m i avg ω
  let S : H → H := weightedBlockOperator m i T ω
  have hω_cc : ∀ k, ω k ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    exact ⟨(hω k).1.le, (hω k).2⟩
  have hBlockAveraged :
      ∀ k : Fin p, AveragedWith (blockAveragingParameter m i avg k)
        (fun x : H_univ ↦ blockComposition m i T k x) := by
    intro k
    -- Each block composition is averaged with the parameter from Proposition 4.46.
    exact block_composition_averaged_with m i T avg hT k
  have hS_averaged : AveragedWith α (fun x : H_univ ↦ S x) := by
    -- Proposition 4.42 turns blockwise averagedness into averagedness of the weighted block
    -- operator with parameter `α`.
    simpa [α, S, weightedBlockAveragingParameter, weightedBlockOperator] using
      averagedWith_weightedSum ω (fun k : Fin p ↦ blockAveragingParameter m i avg k)
        (fun k : Fin p ↦ fun x : H_univ ↦ blockComposition m i T k x) hω_cc hω_sum hBlockAveraged
  have hS_fix_eq :
      Function.fixedPoints S = ⋂ j : I, Function.fixedPoints (T j) := by
    -- The weighted block operator fixes exactly the common fixed points of the original family.
    simpa [S] using
      fixed_points_weighted_block_operator_eq_iInter m i T avg ω hT hFix hω hω_sum hcover
  have hS_fix_nonempty : (Function.fixedPoints S).Nonempty := by
    rcases hFix with ⟨z, hz⟩
    exact ⟨z, by simpa [hS_fix_eq] using hz⟩
  have hlam' : ∀ n, lam n ∈ Set.Icc (0 : ℝ) (1 / α) := by
    intro n
    simpa [α, weightedBlockAveragingParameter, blockAveragingParameter] using hlam n
  have hdiv' :
      Tendsto
        (fun N ↦ ∑ n ∈ Finset.range N, lam n * (1 - α * lam n))
        atTop atTop := by
    simpa [α, weightedBlockAveragingParameter, blockAveragingParameter] using hdiv
  rcases
      exists_tendsto_weakly_to_fixedPoint_of_relaxedOperatorIteration_of_averagedWith
        (T := S) (α := α) (hT := hS_averaged) (lam := lam) (hlam := hlam') hS_fix_nonempty hdiv'
        x₀ with
    ⟨z, hzS, hlim⟩
  refine ⟨z, ?_, ?_⟩
  · -- The fixed-point description places the weak limit in the common fixed-point set.
    simpa [hS_fix_eq] using hzS
  · -- This is exactly the relaxed orbit of the weighted block operator.
    simpa [S, weightedBlockOperator] using hlim

/-- Helper for Example 5.21: each relaxed projector is `(β j / 2)`-averaged on `Set.univ`. -/
private theorem relaxed_projection_averaged_with_on_univ (C : I → Set H)
    (hC_closed : ∀ j, IsClosed (C j)) (hC_convex : ∀ j, Convex ℝ (C j))
    (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ) (j : I)
    (hβj : β j ∈ Set.Ioo (0 : ℝ) 2) :
    AveragedWith (β j / 2)
      (fun x : H_univ ↦ relaxedProjectionFamily C hC_closed hC_convex hC_inter_nonempty β j x) := by
  let P : H → H :=
    projectionPoint (C j)
      (isChebyshev_of_nonempty_isClosed_convex
        (nonempty_component_of_nonempty_iInter C hC_inter_nonempty j)
        (hC_closed j) (hC_convex j))
  have hfirm : IsFirmlyNonexpansiveOn (fun x : H_univ ↦ P x) := by
    intro x y
    have hproj : ‖P x - P y‖ ^ 2 ≤ inner ℝ ((x : H) - y) (P x - P y) := by
      simpa [P, real_inner_comm] using
        norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
          (nonempty_component_of_nonempty_iInter C hC_inter_nonempty j) (hC_closed j)
          (hC_convex j) (x : H) (y : H)
    have hrewrite :
        ((x : H) - P x) - ((y : H) - P y) = ((x : H) - y) - (P x - P y) := by
      abel
    rw [hrewrite]
    have hnorm :
        ‖((x : H) - y) - (P x - P y)‖ ^ 2 =
          ‖(x : H) - y‖ ^ 2 - 2 * inner ℝ ((x : H) - y) (P x - P y) + ‖P x - P y‖ ^ 2 := by
      simpa using norm_sub_sq_real ((x : H) - y) (P x - P y)
    nlinarith [hproj, hnorm]
  have havg_half : AveragedWith (1 / 2 : ℝ) (fun x : H_univ ↦ P x) :=
    averagedWith_half_of_isFirmlyNonexpansiveOn hfirm
  rcases averagedWith_iff.mp havg_half with ⟨_, R, hR, hP⟩
  refine averagedWith_iff.mpr ?_
  refine ⟨by constructor <;> nlinarith [hβj.1, hβj.2], R, hR, ?_⟩
  ext x
  have hPx : P x = (1 - (1 / 2 : ℝ)) • (x : H) + (1 / 2 : ℝ) • R x := by
    simpa using congrFun hP x
  have hPx' :
      projectionPoint (C j)
          (isChebyshev_of_nonempty_isClosed_convex
            (nonempty_component_of_nonempty_iInter C hC_inter_nonempty j)
            (hC_closed j) (hC_convex j)) (x : H) =
        (1 - (1 / 2 : ℝ)) • (x : H) + (1 / 2 : ℝ) • R x := by
    simpa [P] using hPx
  rw [relaxedProjectionFamily_apply]
  rw [hPx']
  calc
    (1 - β j) • (x : H) + β j • ((1 - (1 / 2 : ℝ)) • (x : H) + (1 / 2 : ℝ) • R x)
        =
          (1 - β j) • (x : H) +
            ((β j * (1 - (1 / 2 : ℝ))) • (x : H) + (β j * (1 / 2 : ℝ)) • R x) := by
          rw [smul_add, smul_smul, smul_smul]
    _ =
        ((1 - β j) + β j * (1 - (1 / 2 : ℝ))) • (x : H) + (β j * (1 / 2 : ℝ)) • R x := by
          rw [← add_assoc, ← add_smul]
    _ = (1 - β j / 2) • (x : H) + (β j / 2) • R x := by
          have hcoeff1 : (1 - β j) + β j * (1 - (1 / 2 : ℝ)) = 1 - β j / 2 := by
            ring
          have hcoeff2 : β j * (1 / 2 : ℝ) = β j / 2 := by
            ring
          rw [hcoeff1, hcoeff2]

/-- Helper for Example 5.21: the fixed points of the relaxed projector onto `C j` are exactly
the set `C j`. -/
private theorem fixed_points_relaxed_projection_eq (C : I → Set H)
    (hC_closed : ∀ j, IsClosed (C j)) (hC_convex : ∀ j, Convex ℝ (C j))
    (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ) (j : I)
    (hβj : β j ∈ Set.Ioo (0 : ℝ) 2) :
    Function.fixedPoints (relaxedProjectionFamily C hC_closed hC_convex hC_inter_nonempty β j) =
      C j := by
  let P : H → H :=
    projectionPoint (C j)
      (isChebyshev_of_nonempty_isClosed_convex
        (nonempty_component_of_nonempty_iInter C hC_inter_nonempty j)
        (hC_closed j) (hC_convex j))
  have hfixed_eq : Function.fixedPoints P = C j :=
    fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex
      (nonempty_component_of_nonempty_iInter C hC_inter_nonempty j) (hC_closed j) (hC_convex j)
  ext x
  constructor
  · intro hx
    rw [Function.mem_fixedPoints_iff, relaxedProjectionFamily_apply] at hx
    have hPx : P x = x := by
      have hEq' : β j • P x = β j • x := by
        -- Isolate the projector term from the relaxed fixed-point equation.
        calc
          β j • P x = ((1 - β j) • x + β j • P x) - (1 - β j) • x := by
            simp [sub_eq_add_neg, add_assoc, add_comm]
          _ = x - (1 - β j) • x := by rw [hx]
          _ = β j • x := by
            simpa [sub_eq_add_neg, add_smul]
      have := congrArg (fun y : H ↦ (β j)⁻¹ • y) hEq'
      simpa [ne_of_gt hβj.1, smul_smul] using this
    have hxP : x ∈ Function.fixedPoints P := by
      rw [Function.mem_fixedPoints_iff]
      simpa using hPx
    -- Once the projector fixes `x`, the point lies in `C j`.
    simpa [hfixed_eq] using hxP
  · intro hx
    have hxP : x ∈ Function.fixedPoints P := by
      simpa [hfixed_eq] using hx
    rw [Function.mem_fixedPoints_iff] at hxP
    rw [Function.mem_fixedPoints_iff]
    -- A point of `C j` is fixed by the projector, hence also by its relaxation.
    simpa [relaxedProjectionFamily, P, hxP, sub_eq_add_neg, add_smul]

/-- Helper for Example 5.21: each block averaging parameter from the block-composition theorem
lies in `(0, 1)`. -/
private theorem block_relaxation_parameter_mem_Ioo {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (β : I → ℝ)
    (hβ : ∀ j, β j ∈ Set.Ioo (0 : ℝ) 2) (k : Fin p) :
    (1 / (1 + (∑ l : Fin (m k), (β (i k l) / 2) / (1 - β (i k l) / 2))⁻¹) : ℝ) ∈
      Set.Ioo (0 : ℝ) 1 := by
  have hterm_pos :
      ∀ l : Fin (m k), 0 < (β (i k l) / 2) / (1 - β (i k l) / 2) := by
    intro l
    have hβl : β (i k l) / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> nlinarith [(hβ (i k l)).1, (hβ (i k l)).2]
    exact div_pos hβl.1 (sub_pos.mpr hβl.2)
  have hsum_pos :
      0 < ∑ l : Fin (m k), (β (i k l) / 2) / (1 - β (i k l) / 2) := by
    -- Every summand in the block parameter is positive.
    exact Finset.sum_pos (fun l _ ↦ hterm_pos l) Finset.univ_nonempty
  have hden_pos :
      0 < 1 + (∑ l : Fin (m k), (β (i k l) / 2) / (1 - β (i k l) / 2))⁻¹ := by
    have : 0 <
        (∑ l : Fin (m k), (β (i k l) / 2) / (1 - β (i k l) / 2))⁻¹ := inv_pos.mpr hsum_pos
    linarith
  constructor
  · exact one_div_pos.mpr hden_pos
  · have hden_gt_one :
        1 < 1 + (∑ l : Fin (m k), (β (i k l) / 2) / (1 - β (i k l) / 2))⁻¹ := by
      have : 0 <
          (∑ l : Fin (m k), (β (i k l) / 2) / (1 - β (i k l) / 2))⁻¹ := inv_pos.mpr hsum_pos
      linarith
    -- The reciprocal of a number greater than `1` lies strictly below `1`.
    simpa [one_div] using inv_lt_one_of_one_lt₀ hden_gt_one

/-- Helper for Example 5.21: a positive weighted average of numbers in `(0, 1)` still lies in
`(0, 1)`. -/
private theorem weighted_block_relaxation_parameter_mem_Ioo {p : ℕ+} (ω α : Fin p → ℝ)
    (hω : ∀ k, ω k ∈ Set.Ioc (0 : ℝ) 1) (hω_sum : ∑ k : Fin p, ω k = 1)
    (hα : ∀ k, α k ∈ Set.Ioo (0 : ℝ) 1) :
    (∑ k : Fin p, ω k * α k) ∈ Set.Ioo (0 : ℝ) 1 := by
  let αbar : ℝ := ∑ k : Fin p, ω k * α k
  have hαbar_pos : 0 < αbar := by
    have h0 : 0 < ω 0 * α 0 := mul_pos (hω 0).1 (hα 0).1
    have h0_le : ω 0 * α 0 ≤ αbar := by
      simpa [αbar] using
        (Finset.single_le_sum
          (fun k _ ↦ mul_nonneg (hω k).1.le (hα k).1.le)
          (by simp : (0 : Fin p) ∈ (Finset.univ : Finset (Fin p))))
    exact lt_of_lt_of_le h0 h0_le
  have hαbar_lt : αbar < 1 := by
    let δ : ℝ := ∑ k : Fin p, ω k * (1 - α k)
    have hδ_pos : 0 < δ := by
      have h0 : 0 < ω 0 * (1 - α 0) := by
        exact mul_pos (hω 0).1 (sub_pos.mpr (hα 0).2)
      have h0_le : ω 0 * (1 - α 0) ≤ δ := by
        simpa [δ] using
          (Finset.single_le_sum
            (fun k _ ↦ mul_nonneg (hω k).1.le (sub_nonneg.mpr (hα k).2.le))
            (by simp : (0 : Fin p) ∈ (Finset.univ : Finset (Fin p))))
      exact lt_of_lt_of_le h0 h0_le
    have hsplit : αbar + δ = 1 := by
      calc
        αbar + δ = ∑ k : Fin p, (ω k * α k + ω k * (1 - α k)) := by
          simp [αbar, δ, Finset.sum_add_distrib]
        _ = ∑ k : Fin p, ω k := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          ring
        _ = 1 := hω_sum
    nlinarith
  exact ⟨hαbar_pos, hαbar_lt⟩

/-- Helper for Example 5.21: relaxation parameter `1` turns the relaxed iteration into the usual
Picard iterates. -/
private theorem relaxed_one_eq_iterates {T : H → H} (x₀ : H) :
    relaxedOperatorIteration (fun _ ↦ T) (fun _ ↦ (1 : ℝ)) x₀ = fun n ↦ (T^[n]) x₀ := by
  funext n
  induction n with
  | zero =>
      -- Both recursions start from the same initial point.
      simp [relaxedOperatorIteration]
  | succ n ih =>
      -- A Krasnosel'skii-Mann step with weight `1` is exactly one application of `T`.
      rw [relaxedOperatorIteration_succ, ih]
      simp [Function.iterate_succ_apply', sub_eq_add_neg]

-- Proof sketch: each metric projector onto `C j` is firmly nonexpansive and therefore
-- `(β j / 2)`-averaged after relaxation; the weighted block-composition convergence theorem then
-- applies with `λₙ ≡ 1`, and fixed points of the relaxed projectors are exactly the points of the
-- common intersection.
/-- Example 5.21: for a finite family of closed convex sets with nonempty intersection, the orbit
generated by weighted string averages of the relaxed projectors `Tᵢ = (1 - βᵢ) Id + βᵢ P_{Cᵢ}`
converges weakly to a point of the common intersection. -/
theorem exists_tendsto_weakly_to_point_in_iInter_of_stringAveragedRelaxedProjectionOrbit
    {p : ℕ+} (m : Fin p → ℕ+) (i : (k : Fin p) → Fin (m k) → I) (C : I → Set H)
    (hC_closed : ∀ j, IsClosed (C j)) (hC_convex : ∀ j, Convex ℝ (C j))
    (hC_inter_nonempty : (⋂ j, C j).Nonempty) (β : I → ℝ) (hβ : ∀ j, β j ∈ Set.Ioo (0 : ℝ) 2)
    (ω : Fin p → ℝ) (hω : ∀ k, ω k ∈ Set.Ioc (0 : ℝ) 1) (hω_sum : ∑ k : Fin p, ω k = 1)
    (hcover : Function.Surjective (fun q : Σ k : Fin p, Fin (m k) ↦ i q.1 q.2)) (x₀ : H) :
    ∃ z ∈ ⋂ j, C j,
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (stringAveragedRelaxedProjectionOrbit ω m i C hC_closed hC_convex
              hC_inter_nonempty β x₀ n))
        atTop (𝓝 (toWeakSpace ℝ H z)) := by
  let avg : I → ℝ := fun j ↦ β j / 2
  let ρ : Fin p → ℝ := fun k ↦
    1 / (1 + (∑ l : Fin (m k), avg (i k l) / (1 - avg (i k l)))⁻¹)
  let α : ℝ := ∑ k : Fin p, ω k * ρ k
  have hT :
      ∀ j, AveragedWith (avg j)
        (fun x : H_univ ↦ relaxedProjectionFamily C hC_closed hC_convex hC_inter_nonempty β j x) := by
    intro j
    -- Each relaxed projector is averaged because the underlying metric projector is firmly
    -- nonexpansive.
    simpa [avg] using
      relaxed_projection_averaged_with_on_univ C hC_closed hC_convex hC_inter_nonempty β j (hβ j)
  have hFix :
      ((⋂ j,
        Function.fixedPoints (relaxedProjectionFamily C hC_closed hC_convex hC_inter_nonempty β j))
        : Set H).Nonempty := by
    have hC_inter_nonempty' := hC_inter_nonempty
    rcases hC_inter_nonempty with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Set.mem_iInter]
    intro j
    -- A point in the common intersection is fixed by every relaxed projector.
    have hzj : z ∈ C j := (Set.mem_iInter.mp hz) j
    rw [Function.mem_fixedPoints_iff]
    have hprojz :
        projectionPoint (C j)
            (isChebyshev_of_nonempty_isClosed_convex
              (nonempty_component_of_nonempty_iInter C hC_inter_nonempty' j)
              (hC_closed j) (hC_convex j)) z = z :=
      projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex
        (nonempty_component_of_nonempty_iInter C hC_inter_nonempty' j) (hC_closed j) (hC_convex j) hzj
    simpa [relaxedProjectionFamily, sub_eq_add_neg, add_smul, hprojz]
  let P : I → H → H := fun j ↦
    projectionPoint (C j)
      (isChebyshev_of_nonempty_isClosed_convex
        (nonempty_component_of_nonempty_iInter C hC_inter_nonempty j)
        (hC_closed j) (hC_convex j))
  have hρ :
      ∀ k : Fin p, ρ k ∈ Set.Ioo (0 : ℝ) 1 := by
    intro k
    -- The block parameter is `B / (1 + B)` in disguise with `B > 0`.
    simpa [ρ, avg, div_eq_mul_inv] using block_relaxation_parameter_mem_Ioo m i β hβ k
  have hα : α ∈ Set.Ioo (0 : ℝ) 1 := by
    -- A positive weighted average of numbers in `(0, 1)` stays in `(0, 1)`.
    exact weighted_block_relaxation_parameter_mem_Ioo ω ρ hω hω_sum hρ
  have hlam :
      ∀ n : ℕ,
        (1 : ℝ) ∈
          Set.Icc (0 : ℝ)
            (1 / ∑ k : Fin p, ω k * (1 / (1 + (∑ l : Fin (m k), avg (i k l) / (1 - avg (i k l)))⁻¹))) := by
    intro n
    constructor
    · norm_num
    · have hα_ne : α ≠ 0 := ne_of_gt hα.1
      have h_one_le_inv : (1 : ℝ) ≤ 1 / α := by
        simpa [one_div] using (one_le_inv₀ hα.1).2 hα.2.le
      simpa [α, ρ] using h_one_le_inv
  have hdiv :
      Tendsto
        (fun N ↦ ∑ n ∈ Finset.range N, (1 : ℝ) * (1 - α * 1))
        atTop atTop := by
    have hconst_pos : 0 < (1 : ℝ) * (1 - α * 1) := by
      simpa using sub_pos.mpr hα.2
    -- A positive constant summand yields divergence of the partial sums to `+∞`.
    convert Tendsto.const_mul_atTop hconst_pos tendsto_natCast_atTop_atTop using 1
    ext N
    simp
    ring
  rcases
      exists_tendsto_weakly_to_common_fixedPoint_of_krasnoselskiiMann_weightedBlockComposition
        (m := m) (i := i)
        (T := relaxedProjectionFamily C hC_closed hC_convex hC_inter_nonempty β)
        (avg := avg) (ω := ω) (hT := hT) (hFix := hFix) (hω := hω) (hω_sum := hω_sum)
        (hcover := hcover) (lam := fun _ ↦ (1 : ℝ)) (hlam := hlam)
        (hdiv := by simpa [α, ρ] using hdiv) (x₀ := x₀) with
    ⟨z, hz, hlim⟩
  refine ⟨z, ?_, ?_⟩
  · rw [Set.mem_iInter]
    intro j
    -- Convert a relaxed fixed point back to a projector fixed point, then to membership in `C j`.
    have hzfix : relaxedProjectionFamily C hC_closed hC_convex hC_inter_nonempty β j z = z :=
      (Set.mem_iInter.mp hz) j
    have hPz : P j z = z := by
      have hEq' : β j • P j z = β j • z := by
        rw [relaxedProjectionFamily_apply] at hzfix
        calc
          β j • P j z = ((1 - β j) • z + β j • P j z) - (1 - β j) • z := by
            simp [sub_eq_add_neg, add_assoc, add_comm]
          _ = z - (1 - β j) • z := by rw [hzfix]
          _ = β j • z := by
            simpa [sub_eq_add_neg, add_smul]
      have := congrArg (fun y : H ↦ (β j)⁻¹ • y) hEq'
      simpa [P, ne_of_gt (hβ j).1, smul_smul] using this
    have hzP : z ∈ Function.fixedPoints (P j) := by
      rw [Function.mem_fixedPoints_iff]
      simpa using hPz
    have hPfix_eq : Function.fixedPoints (P j) = C j :=
      fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex
        (nonempty_component_of_nonempty_iInter C hC_inter_nonempty j) (hC_closed j) (hC_convex j)
    simpa [P, hPfix_eq] using hzP
  · -- Route correction: after the block-composition theorem, identify the relaxed orbit with the
    -- Picard iterates of the string-averaged relaxed projection operator.
    simpa [stringAveragedRelaxedProjectionOrbit, stringAveragedRelaxedProjectionOperator,
      stringBlockCompositionOperator, blockComposition, weightedBlockOperator,
      relaxed_one_eq_iterates, weightedOperatorAverage_apply] using hlim

end
