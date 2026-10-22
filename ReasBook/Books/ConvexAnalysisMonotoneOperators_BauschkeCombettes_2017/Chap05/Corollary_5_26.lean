/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Corollary_4_51
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_44
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_16

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H_univ" => (Set.univ : Set H)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A nonempty common intersection makes every component set nonempty. -/
private theorem nonempty_component_of_nonempty_iInter {m : ℕ} {C : Fin (m + 1) → Set H}
    (hC_inter_nonempty : (⋂ i, C i).Nonempty) (i : Fin (m + 1)) :
    (C i).Nonempty := by
  -- Extract one point from the common intersection and project its membership to the `i`-th set.
  rcases hC_inter_nonempty with ⟨x, hx⟩
  exact ⟨x, (Set.mem_iInter.mp hx) i⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 5.26: lifting a finite ordered composition to `Set.univ` preserves the
ambient value after coercion. -/
@[simp] private theorem finiteComposition_univFamily_coe :
    {m : ℕ} → (S : Fin m → H → H) → ∀ x : H_univ,
      ((finiteComposition (fun i ↦ fun y : H_univ ↦ ⟨S i y, Set.mem_univ _⟩) x : H_univ) : H) =
        finiteComposition S x
  | 0, _, _ => rfl
  | _ + 1, S, x => by
      -- Expand the head-tail composition on both sides and rewrite the lifted tail recursively.
      rw [finiteComposition_succ, finiteComposition_succ]
      simp only [Function.comp_apply]
      exact congrArg (S 0) (finiteComposition_univFamily_coe (S := fun i ↦ S i.succ) (x := x))

/-- Helper for Corollary 5.26: every point of a nonempty closed convex set is fixed by its metric
projection. -/
private theorem projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {x : H}
    (hx : x ∈ C) :
    projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x = x := by
  have hxproj :
      x =
        projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x := by
    -- The characterization of the metric projection closes the pointwise fixed-point relation.
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mpr <| by
          refine ⟨hx, ?_⟩
          intro y hy
          simp
  simpa using hxproj.symm

/-- Helper for Corollary 5.26: the fixed-point set of the metric projector onto a nonempty closed
convex set is exactly that set. -/
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
    simpa [hx] using
      projectionPoint_mem C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  · intro hx
    rw [Function.mem_fixedPoints_iff]
    exact projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex hx

omit [CompleteSpace H] in
/-- Helper for Corollary 5.26: the reflected squared-norm gap expands to four times the firm
nonexpansiveness defect. -/
private lemma reflection_norm_gap_eq_four_mul (a b : H) :
    ‖a‖ ^ 2 - ‖(2 : ℝ) • b - a‖ ^ 2 = 4 * (inner ℝ a b - ‖b‖ ^ 2) := by
  have htwo : (2 : ℝ) • b = b + b := by
    simpa using (two_smul ℝ b)
  rw [htwo]
  have hsub : ‖a‖ ^ 2 - ‖(b + b) - a‖ ^ 2 = 2 * inner ℝ (b + b) a - ‖b + b‖ ^ 2 := by
    -- Expand the reflected square by the standard Hilbert-space norm identity.
    nlinarith [norm_sub_sq_real (b + b) a]
  have hnorm : ‖b + b‖ ^ 2 = 4 * ‖b‖ ^ 2 := by
    -- The doubled point contributes exactly four copies of `‖b‖²`.
    rw [norm_add_sq_real, real_inner_self_eq_norm_sq]
    ring
  -- Reassemble the expansion and commute the real inner product once.
  rw [hsub, hnorm, inner_add_left, real_inner_comm b a]
  ring

/-- Helper for Corollary 5.26: the fixed points of the ordered composite projector are exactly the
common intersection of the constraint sets. -/
private theorem fixedPoints_projectorComposition_eq_iInter {m : ℕ} (C : Fin (m + 1) → Set H)
    (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) (hC_inter_nonempty : (⋂ i, C i).Nonempty) :
    Function.fixedPoints
        (finiteComposition fun i ↦
          projectionPoint (C i)
            (isChebyshev_of_nonempty_isClosed_convex
              (hC_nonempty i) (hC_closed i) (hC_convex i))) =
      ⋂ i, C i := by
  let T : Fin (m + 1) → H_univ → H_univ := fun i x ↦
    ⟨projectionPoint (C i)
        (isChebyshev_of_nonempty_isClosed_convex
          (hC_nonempty i) (hC_closed i) (hC_convex i)) x,
      Set.mem_univ _⟩
  have hAveraged :
      ∀ i : Fin (m + 1), ∃ α, AveragedWith α (fun x : H_univ ↦ (T i x : H)) := by
    intro i
    refine ⟨1 / 2, ?_⟩
    let P : H_univ → H := fun x ↦
      projectionPoint (C i)
        (isChebyshev_of_nonempty_isClosed_convex
          (hC_nonempty i) (hC_closed i) (hC_convex i)) x
    let R : H_univ → H := fun x ↦ (2 : ℝ) • P x - (x : H)
    refine averagedWith_iff.mpr ?_
    refine ⟨by norm_num, R, ?_, ?_⟩
    · refine LipschitzWith.of_dist_le_mul ?_
      intro x y
      let a : H := (x : H) - y
      let b : H := P x - P y
      have hfirm :
          ‖b‖ ^ 2 ≤ inner ℝ a b := by
        simpa [P, a, b, real_inner_comm] using
          norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
            (hC_nonempty i) (hC_closed i) (hC_convex i) (x : H) (y : H)
      have hsq :
          ‖(2 : ℝ) • b - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
        nlinarith [reflection_norm_gap_eq_four_mul a b, hfirm]
      have hreflect : R x - R y = (2 : ℝ) • b - a := by
        dsimp [R, P, a, b]
        rw [sub_eq_add_neg, sub_eq_add_neg, smul_sub]
        abel_nf
      have hdist : ‖R x - R y‖ ≤ ‖a‖ := by
        rw [hreflect]
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
      simpa [Subtype.dist_eq, dist_eq_norm, one_mul, a] using hdist
    · funext x
      dsimp [R, P]
      have hhalf_eq : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
        norm_num
      calc
        projectionPoint (C i)
            (isChebyshev_of_nonempty_isClosed_convex
              (hC_nonempty i) (hC_closed i) (hC_convex i)) x
            = (1 / 2 : ℝ) •
                ((2 : ℝ) •
                  projectionPoint (C i)
                    (isChebyshev_of_nonempty_isClosed_convex
                      (hC_nonempty i) (hC_closed i) (hC_convex i)) x) := by
                rw [smul_smul]
                norm_num
        _ = (1 / 2 : ℝ) • (x : H) +
              ((1 / 2 : ℝ) •
                ((2 : ℝ) •
                  projectionPoint (C i)
                    (isChebyshev_of_nonempty_isClosed_convex
                      (hC_nonempty i) (hC_closed i) (hC_convex i)) x) -
                (1 / 2 : ℝ) • (x : H)) := by
              abel_nf
        _ = (1 - (1 / 2 : ℝ)) • (x : H) + (1 / 2 : ℝ) • R x := by
              rw [hhalf_eq, smul_sub]
  have hfix :
      Set.Nonempty (⋂ i, Function.fixedPoints (T i) : Set H_univ) := by
    rcases hC_inter_nonempty with ⟨z, hz⟩
    refine ⟨⟨z, Set.mem_univ _⟩, ?_⟩
    rw [Set.mem_iInter]
    intro i
    rw [Function.mem_fixedPoints_iff]
    apply Subtype.ext
    -- A point in the common intersection is fixed by each individual metric projector.
    have hzi : z ∈ C i := (Set.mem_iInter.mp hz) i
    exact projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex
      (hC_nonempty i) (hC_closed i) (hC_convex i) hzi
  have hfix_eq :
      Function.fixedPoints (finiteComposition T) = ⋂ i, Function.fixedPoints (T i) :=
    fixedPoints_finiteComposition_eq_iInter_fixedPoints_of_averagedWith
      (T := T) hAveraged hfix
  ext z
  constructor
  · intro hz
    have hz_univ :
        (⟨z, Set.mem_univ _⟩ : H_univ) ∈ Function.fixedPoints (finiteComposition T) := by
      rw [Function.mem_fixedPoints_iff] at hz ⊢
      apply Subtype.ext
      -- Reinterpret the ambient fixed-point equation in the lifted `Set.univ` setting.
      simpa [T] using hz
    have hz_iInter :
        (⟨z, Set.mem_univ _⟩ : H_univ) ∈ ⋂ i, Function.fixedPoints (T i) := by
      simpa [hfix_eq] using hz_univ
    rw [Set.mem_iInter]
    intro i
    have hz_fix_i : (⟨z, Set.mem_univ _⟩ : H_univ) ∈ Function.fixedPoints (T i) :=
      (Set.mem_iInter.mp hz_iInter) i
    rw [Function.mem_fixedPoints_iff] at hz_fix_i
    -- Each coordinate fixed-point relation identifies `z` as a point of `C i`.
    have hz_eq :
        projectionPoint (C i)
            (isChebyshev_of_nonempty_isClosed_convex
              (hC_nonempty i) (hC_closed i) (hC_convex i)) z = z :=
      congrArg Subtype.val hz_fix_i
    simpa [hz_eq] using
      projectionPoint_mem (C i)
        (isChebyshev_of_nonempty_isClosed_convex
          (hC_nonempty i) (hC_closed i) (hC_convex i)) z
  · intro hz
    have hz_iInter :
        (⟨z, Set.mem_univ _⟩ : H_univ) ∈ ⋂ i, Function.fixedPoints (T i) := by
      rw [Set.mem_iInter]
      intro i
      rw [Function.mem_fixedPoints_iff]
      apply Subtype.ext
      -- Membership in `C i` gives the projector fixed-point relation at index `i`.
      have hzi : z ∈ C i := (Set.mem_iInter.mp hz) i
      exact projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex
        (hC_nonempty i) (hC_closed i) (hC_convex i) hzi
    have hz_univ :
        (⟨z, Set.mem_univ _⟩ : H_univ) ∈ Function.fixedPoints (finiteComposition T) := by
      simpa [hfix_eq] using hz_iInter
    rw [Function.mem_fixedPoints_iff] at hz_univ ⊢
    -- Coercing the lifted fixed-point equation returns the ambient composite-projector equation.
    simpa [T] using congrArg Subtype.val hz_univ

/-- Helper for Corollary 5.26: a metric projector onto a nonempty closed convex set is
`1 / 2`-averaged on `Set.univ`. -/
private theorem projector_averaged_half {C : Set H} (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    AveragedWith (1 / 2 : ℝ)
      (fun x : H_univ ↦
        projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x) := by
  let P : H_univ → H := fun x ↦
    projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  let R : H_univ → H := fun x ↦ (2 : ℝ) • P x - (x : H)
  refine averagedWith_iff.mpr ?_
  refine ⟨by norm_num, R, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    let a : H := (x : H) - y
    let b : H := P x - P y
    have hfirm :
        ‖b‖ ^ 2 ≤ inner ℝ a b := by
      simpa [P, a, b, real_inner_comm] using
        norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex (x : H) (y : H)
    have hsq :
        ‖(2 : ℝ) • b - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      nlinarith [reflection_norm_gap_eq_four_mul a b, hfirm]
    have hreflect : R x - R y = (2 : ℝ) • b - a := by
      dsimp [R, P, a, b]
      rw [sub_eq_add_neg, sub_eq_add_neg, smul_sub]
      abel_nf
    have hdist : ‖R x - R y‖ ≤ ‖a‖ := by
      rw [hreflect]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
    simpa [Subtype.dist_eq, dist_eq_norm, one_mul, a] using hdist
  · funext x
    dsimp [R, P]
    have hhalf_eq : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    calc
      P x = (1 / 2 : ℝ) • ((2 : ℝ) • P x) := by
              rw [smul_smul]
              norm_num
      _ = (1 / 2 : ℝ) • (x : H) +
            ((1 / 2 : ℝ) • ((2 : ℝ) • P x) - (1 / 2 : ℝ) • (x : H)) := by
            abel_nf
      _ = (1 - (1 / 2 : ℝ)) • (x : H) + (1 / 2 : ℝ) • R x := by
            rw [hhalf_eq, smul_sub]

/-- Helper for Corollary 5.26: the ordered composite of the metric projectors is an averaged
operator on the whole space. -/
private theorem projectorComposition_averaged {m : ℕ} (C : Fin (m + 1) → Set H)
    (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) :
    ∃ α,
      AveragedWith α
        (fun x : H_univ ↦
          finiteComposition (fun i ↦
            projectionPoint (C i)
              (isChebyshev_of_nonempty_isClosed_convex
                (hC_nonempty i) (hC_closed i) (hC_convex i))) x) := by
  cases m with
  | zero =>
      -- The singleton composition is exactly one projector.
      exact
        ⟨1 / 2, by
          simpa [finiteComposition] using
            projector_averaged_half (hC_nonempty 0) (hC_closed 0) (hC_convex 0)⟩
  | succ n =>
      have hm2 : 2 ≤ n + 2 := by
        omega
      refine ⟨1 / (1 + (∑ i : Fin (n + 2), ((1 / 2 : ℝ) / (1 - 1 / 2)))⁻¹), ?_⟩
      -- Proposition 4.46 applies directly to the lifted projector family on `Set.univ`.
      simpa [finiteComposition_univFamily_coe] using
        averagedWith_compose_fin (D := H_univ) hm2 ⟨0, Set.mem_univ _⟩
          (fun _ : Fin (n + 2) ↦ (1 / 2 : ℝ))
          (fun i ↦ fun x : H_univ ↦
            ⟨projectionPoint (C i)
                (isChebyshev_of_nonempty_isClosed_convex
                  (hC_nonempty i) (hC_closed i) (hC_convex i)) x,
              Set.mem_univ _⟩)
          (fun i ↦ by
            simpa using projector_averaged_half
              (hC_nonempty i) (hC_closed i) (hC_convex i))

omit [CompleteSpace H] in
/-- Helper for Corollary 5.26: relaxation parameter `1` turns the relaxed iteration into the usual
Picard iterates. -/
private theorem relaxed_one_eq_iterates {T : H → H} (x₀ : H) :
    relaxedOperatorIteration (fun _ ↦ T) (fun _ ↦ (1 : ℝ)) x₀ = fun n ↦ (T^[n]) x₀ := by
  funext n
  induction n with
  | zero =>
      -- Both recursions start from the same initial point.
      simp [relaxedOperatorIteration]
  | succ n ih =>
      -- The Krasnosel'skii-Mann step with weight `1` is exactly one application of `T`.
      rw [relaxedOperatorIteration_succ, ih]
      simp [Function.iterate_succ_apply', sub_eq_add_neg]

-- Proof sketch: first identify the common fixed-point set of the ordered projector composition
-- with `⋂ i, C i`. Next prove that the composition is averaged by composing the half-averaged
-- projector factors. Apply the averaged-operator weak convergence theorem with constant
-- relaxation parameter `1`, and finally rewrite the relaxed orbit as the Picard iterates of the
-- projector composition.
/-- Corollary 5.26: if a finite family of closed convex sets in a real Hilbert space has nonempty
intersection, then the Picard iterates of the ordered composition of their metric projectors
converge weakly to a point in the common intersection. -/
theorem exists_tendsto_weakly_to_point_in_iInter_of_cyclicProjection {m : ℕ}
    (C : Fin (m + 1) → Set H) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) (hC_inter_nonempty : (⋂ i, C i).Nonempty) (x₀ : H) :
    ∃ z ∈ ⋂ i, C i,
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (((finiteComposition fun i ↦
                projectionPoint (C i)
                  (isChebyshev_of_nonempty_isClosed_convex
                    (nonempty_component_of_nonempty_iInter hC_inter_nonempty i)
                    (hC_closed i) (hC_convex i)))^[n]) x₀))
        atTop (𝓝 (toWeakSpace ℝ H z)) := by
  let hC_nonempty : ∀ i, (C i).Nonempty :=
    fun i ↦ nonempty_component_of_nonempty_iInter hC_inter_nonempty i
  let P : H → H := finiteComposition fun i ↦
    projectionPoint (C i)
      (isChebyshev_of_nonempty_isClosed_convex
        (hC_nonempty i) (hC_closed i) (hC_convex i))
  rcases projectorComposition_averaged C hC_nonempty hC_closed hC_convex with ⟨α, hP_avg⟩
  have hfix_eq : Function.fixedPoints P = ⋂ i, C i :=
    fixedPoints_projectorComposition_eq_iInter
      C hC_nonempty hC_closed hC_convex hC_inter_nonempty
  have hfix : (Function.fixedPoints P).Nonempty := by
    rcases hC_inter_nonempty with ⟨z, hz⟩
    -- The fixed-point identification produces the witness needed by Proposition 5.16.
    exact ⟨z, by simpa [P, hfix_eq] using hz⟩
  have hα_lt_one : α < 1 := (AveragedWith.mem_Ioo hP_avg).2
  have hdiv :
      Tendsto
        (fun N ↦ ∑ n ∈ Finset.range N, (1 : ℝ) * (1 - α * 1))
        atTop atTop := by
    have hconst_pos : 0 < (1 : ℝ) * (1 - α * 1) := by
      nlinarith
    -- A positive constant summand yields divergence of the partial sums to `+∞`.
    convert Tendsto.const_mul_atTop hconst_pos tendsto_natCast_atTop_atTop using 1
    ext N
    simp
    ring
  rcases
      exists_tendsto_weakly_to_fixedPoint_of_relaxedOperatorIteration_of_averagedWith
        (hT := hP_avg) (lam := fun _ ↦ (1 : ℝ))
        (hlam := by
          have hα_pos : 0 < α := (AveragedWith.mem_Ioo hP_avg).1
          have hα_ne : α ≠ 0 := ne_of_gt hα_pos
          have h_one_le_inv : (1 : ℝ) ≤ 1 / α := by
            field_simp [hα_ne]
            linarith
          intro n
          constructor
          · norm_num
          · exact h_one_le_inv)
        hfix hdiv x₀ with
    ⟨z, hz, hlim⟩
  refine ⟨z, ?_, ?_⟩
  · -- The weak limit lies in the common intersection because it is a fixed point of `P`.
    simpa [P, hfix_eq] using hz
  · -- Relaxation parameter `1` identifies the averaged iteration with the Picard orbit of `P`.
    simpa [P, relaxed_one_eq_iterates] using hlim

end
