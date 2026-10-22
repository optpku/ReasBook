/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_42
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_47
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Corollary_4_51
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_16

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function
open scoped BigOperators Topology

universe u v

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type v}

local notation "H_univ" => (Set.univ : Set H)

/-- Helper for Corollary 5.19: the averaging parameter associated with a single ordered block of
operators. -/
private noncomputable def blockAveragingParameter {p : ℕ+}
    (m : Fin p → ℕ+) (i : (k : Fin p) → Fin (m k) → I)
    (avg : I → ℝ) (k : Fin p) : ℝ :=
  1 / (1 + (∑ l : Fin (m k), avg (i k l) / (1 - avg (i k l)))⁻¹)

/-- Helper for Corollary 5.19: the weighted average of the block averaging parameters. -/
private noncomputable def weightedBlockAveragingParameter {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (avg : I → ℝ) (ω : Fin p → ℝ) : ℝ :=
  ∑ k : Fin p, ω k * blockAveragingParameter m i avg k

/-- Helper for Corollary 5.19: the ordered composition attached to a single block. -/
private noncomputable abbrev blockComposition {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H) (k : Fin p) : H → H :=
  finiteComposition (fun l : Fin (m k) ↦ T (i k l))

/-- Helper for Corollary 5.19: the weighted average of the ordered block compositions. -/
private noncomputable def weightedBlockOperator {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H) (ω : Fin p → ℝ) : H → H :=
  fun x ↦
    weightedOperatorAverage ω
      (fun k : Fin p ↦ fun y : H_univ ↦ blockComposition m i T k y)
      ⟨x, Set.mem_univ _⟩

/-- Helper for Corollary 5.19: a family of ambient self-maps lifts canonically to the whole-space
subtype `Set.univ`. -/
private noncomputable def liftUnivFamily {m : ℕ} (T : Fin m → H → H) :
    Fin m → H_univ → H_univ :=
  fun j x ↦ ⟨T j (x : H), Set.mem_univ _⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 5.19: the lifted family coerces back to the original ambient self-maps. -/
@[simp] private theorem liftUnivFamily_coe {m : ℕ} (T : Fin m → H → H) (j : Fin m) (x : H_univ) :
    ((liftUnivFamily T j x : H_univ) : H) = T j (x : H) :=
  rfl

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 5.19: lifting a finite ordered composition to `Set.univ` preserves its
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

/-- Helper for Corollary 5.19: the singleton textbook block parameter simplifies to the original
averaging parameter. -/
private theorem inv_one_add_inv_eq_of_mem_Ioo {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    1 / (1 + (a / (1 - a))⁻¹) = a := by
  have ha0 : a ≠ 0 := ne_of_gt ha.1
  have h1a0 : 1 - a ≠ 0 := sub_ne_zero.mpr (ne_of_lt ha.2).symm
  have h_one_sub_pos : 0 < 1 - a := sub_pos.mpr ha.2
  have hfrac_pos : 0 < a / (1 - a) := by
    exact div_pos ha.1 h_one_sub_pos
  have hsum0 : 1 + (a / (1 - a))⁻¹ ≠ 0 := by
    have hfrac_inv_pos : 0 < (a / (1 - a))⁻¹ := inv_pos.mpr hfrac_pos
    have : 0 < 1 + (a / (1 - a))⁻¹ := by
      linarith
    exact ne_of_gt this
  field_simp [ha0, h1a0, hsum0]
  ring

/-- Helper for Corollary 5.19: a singleton block carries the original averaging parameter. -/
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

/-- Helper for Corollary 5.19: a singleton block composition is just the corresponding original
operator. -/
private theorem finiteComposition_const_eq_of_card_one (f : H → H) {n : ℕ} (hn : n = 1) :
    finiteComposition (fun _ : Fin n ↦ f) = f := by
  cases hn
  funext x
  simp [finiteComposition, Function.comp_apply]

/-- Helper for Corollary 5.19: a singleton block composition is just the corresponding original
operator. -/
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
  -- Collapse the one-term ordered composition to its unique factor.
  rw [blockComposition, hblock]
  exact finiteComposition_const_eq_of_card_one (T (i k 0)) hm1

/-- Helper for Corollary 5.19: each ordered block composition is averaged with the textbook
parameter attached to that block. -/
private theorem block_composition_averaged_with {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H) (avg : I → ℝ)
    (hT : ∀ j, AveragedWith (avg j) (fun x : H_univ ↦ T j x)) (k : Fin p) :
    AveragedWith (blockAveragingParameter m i avg k) (fun x : H_univ ↦ blockComposition m i T k x) := by
  by_cases hm1 : (m k : ℕ) = 1
  · -- Route correction: avoid dependent elimination on `m k = 1` by collapsing the singleton
    -- block directly at the unique index `0`.
    have hparam_eq :
        blockAveragingParameter m i avg k = avg (i k 0) :=
      block_averaging_parameter_eq_of_card_one m i T avg hT k hm1
    have hblock_eq : blockComposition m i T k = T (i k 0) :=
      block_composition_eq_of_card_one m i T k hm1
    -- A singleton block is just the corresponding original operator.
    rw [hparam_eq, hblock_eq]
    exact hT (i k 0)
  · have hm2 : 2 ≤ (m k : ℕ) := by
      have hmpos : 0 < (m k : ℕ) := (m k).pos
      omega
    have hcomp :
        AveragedWith (blockAveragingParameter m i avg k)
          (fun x : H_univ ↦
            ((finiteComposition (liftUnivFamily (fun l : Fin (m k) ↦ T (i k l))) x : H_univ) : H)) := by
      -- Proposition 4.46 applies to the lifted block family on `Set.univ`.
      simpa [blockAveragingParameter] using
        averagedWith_compose_fin (D := H_univ) hm2 ⟨0, Set.mem_univ _⟩
          (fun l : Fin (m k) ↦ avg (i k l))
          (liftUnivFamily (fun l : Fin (m k) ↦ T (i k l)))
          (fun l ↦ by simpa using hT (i k l))
    -- Coercing the lifted composition recovers the ambient block operator.
    simpa [blockComposition, finiteComposition_liftUnivFamily_coe] using hcomp

/-- Helper for Corollary 5.19: the fixed points of a block composition are exactly the common
fixed points of the operators appearing in that block. -/
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
    -- A common fixed point of the original family is fixed by every lifted block entry.
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
      -- Each ambient block entry fixes `x`, so the lifted block entry fixes `⟨x, _⟩`.
      have hxl : T (i k l) x = x := (Set.mem_iInter.mp hx) l
      simpa [U] using hxl
    have hx_univ : (⟨x, Set.mem_univ _⟩ : H_univ) ∈ Function.fixedPoints (finiteComposition U) := by
      simpa [hfix_eq] using hx_iInter
    rw [Function.mem_fixedPoints_iff] at hx_univ ⊢
    -- Coercing the lifted composition fixed-point equation recovers the ambient block equation.
    simpa [U, blockComposition, finiteComposition_liftUnivFamily_coe] using congrArg Subtype.val hx_univ

/-- Helper for Corollary 5.19: surjectivity of the block index map rewrites the nested blockwise
intersection back to the common intersection over the original family. -/
private theorem iInter_blocks_eq_iInter_of_surjective {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (A : I → Set H)
    (hcover : Surjective (fun q : Σ k : Fin p, Fin (m k) ↦ i q.1 q.2)) :
    (⋂ k : Fin p, ⋂ l : Fin (m k), A (i k l)) = ⋂ j : I, A j := by
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro hx j
    rcases hcover j with ⟨q, rfl⟩
    exact hx q.1 q.2
  · intro hx k l
    exact hx (i k l)

/-- Helper for Corollary 5.19: the weighted block operator has as fixed points exactly the common
fixed points of the original family. -/
private theorem fixed_points_weighted_block_operator_eq_iInter {p : ℕ+} (m : Fin p → ℕ+)
    (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H) (avg : I → ℝ) (ω : Fin p → ℝ)
    (hT : ∀ j, AveragedWith (avg j) (fun x : H_univ ↦ T j x))
    (hFix : (⋂ j, Function.fixedPoints (T j)).Nonempty) (hω : ∀ k, ω k ∈ Set.Ioc (0 : ℝ) 1)
    (hω_sum : ∑ k : Fin p, ω k = 1)
    (hcover : Surjective (fun q : Σ k : Fin p, Fin (m k) ↦ i q.1 q.2)) :
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
      -- The common fixed point lies in the blockwise intersection, hence fixes the block composition.
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
    -- Coercing the subtype fixed-point equation returns the ambient weighted block operator.
    simpa [weightedBlockOperator] using hxWithin

-- Proof sketch: identify each block composition as averaged with the textbook parameter, pass to
-- their weighted average, identify the corresponding fixed-point set with the common fixed points
-- of the original family, and then invoke Proposition 5.16 for the relaxed iteration of that
-- single weighted block operator.
/-- Corollary 5.19: for a finite weighted family of finite ordered compositions of averaged
nonexpansive self-maps on a real Hilbert space, if the block index map covers the whole family and
`∑ λₙ (1 - α λₙ) = +∞` with
`α = ∑ k, ω k * (1 / (1 + (∑ l, avg (i k l) / (1 - avg (i k l)))⁻¹))`, then the relaxed orbit of
the corresponding weighted block operator, written canonically via `weightedOperatorAverage`,
converges weakly to a common fixed point of the original family. -/
theorem exists_tendsto_weakly_to_common_fixedPoint_of_krasnoselskiiMann_weightedBlockComposition
    {p : ℕ+} (m : Fin p → ℕ+) (i : (k : Fin p) → Fin (m k) → I) (T : I → H → H)
    (avg : I → ℝ) (ω : Fin p → ℝ)
    (hT : ∀ j, AveragedWith (avg j) (fun x : (Set.univ : Set H) ↦ T j x))
    (hFix : (⋂ j, fixedPoints (T j)).Nonempty)
    (hω : ∀ k, ω k ∈ Set.Ioc (0 : ℝ) 1) (hω_sum : ∑ k : Fin p, ω k = 1)
    (hcover : Surjective (fun q : Σ k : Fin p, Fin (m k) ↦ i q.1 q.2))
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
            fun y : (Set.univ : Set H) ↦
              finiteComposition (fun l : Fin (m k) ↦ T (i k l)) y)
          ⟨x, by simp⟩
    ∃ z ∈ ⋂ j, fixedPoints (T j),
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
    -- Proposition 4.42 turns the blockwise averagedness into averagedness of the weighted block
    -- operator with parameter `α`.
    simpa [α, S, weightedBlockAveragingParameter, weightedBlockOperator] using
      averagedWith_weightedSum ω (fun k : Fin p ↦ blockAveragingParameter m i avg k)
        (fun k : Fin p ↦ fun x : H_univ ↦ blockComposition m i T k x) hω_cc hω_sum hBlockAveraged
  have hS_fix_eq :
      Function.fixedPoints S = ⋂ j : I, Function.fixedPoints (T j) := by
    -- The weighted block operator fixes exactly the common fixed points of the original family.
    simpa [S] using fixed_points_weighted_block_operator_eq_iInter m i T avg ω hT hFix hω hω_sum
      hcover
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
  · -- The fixed-point description places the weak limit in the common intersection.
    simpa [hS_fix_eq] using hzS
  · -- The relaxed orbit in Proposition 5.16 is exactly the orbit in the theorem statement.
    simpa [S, weightedBlockOperator] using hlim

end
