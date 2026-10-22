/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_23

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function
open scoped InnerProductSpace Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H_univ" => (Set.univ : Set H)

/-- The canonical family of metric projectors associated with a finite family of nonempty closed
convex sets in a real Hilbert space. -/
noncomputable def pocsProjectorFamily {m : ℕ} (C : Fin (m + 1) → Set H)
    (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) :
    Fin (m + 1) → H → H :=
  fun i ↦
    projectionPoint (C i)
      (isChebyshev_of_nonempty_isClosed_convex (hC_nonempty i) (hC_closed i) (hC_convex i))

/-- The ordered composite projector used by the POCS algorithm. -/
noncomputable abbrev pocsOperator {m : ℕ} (C : Fin (m + 1) → Set H)
    (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) :
    H → H :=
  finiteComposition (pocsProjectorFamily C hC_nonempty hC_closed hC_convex)

/-- The POCS orbit obtained by iterating the composite projector from the initial point `x₀`. -/
noncomputable def pocsOrbit {m : ℕ} (C : Fin (m + 1) → Set H)
    (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) (x₀ : H) :
  ℕ → H :=
  fun n ↦ ((pocsOperator C hC_nonempty hC_closed hC_convex)^[n]) x₀

/-- Helper for Corollary 5.24: a family of ambient self-maps lifts canonically to the whole-space
subtype `Set.univ`. -/
private noncomputable def liftUnivFamily {m : ℕ} (T : Fin m → H → H) :
    Fin m → H_univ → H_univ :=
  fun i x ↦ ⟨T i (x : H), Set.mem_univ _⟩

-- Proof sketch: unfold `pocsOrbit`, use the standard iterate identity
-- `(f^[n + 1]) x₀ = f ((f^[n]) x₀)`, and specialize it to the composite POCS operator.
/-- The POCS orbit satisfies the textbook recursion `x_{n+1} = (P₁ ∘ ··· ∘ P_m) x_n`. -/
theorem pocsOrbit_succ {m : ℕ} (C : Fin (m + 1) → Set H)
    (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) (x₀ : H) (n : ℕ) :
    pocsOrbit C hC_nonempty hC_closed hC_convex x₀ (n + 1) =
      pocsOperator C hC_nonempty hC_closed hC_convex
        (pocsOrbit C hC_nonempty hC_closed hC_convex x₀ n) := by
  -- Rewrite the successor iterate of the composite projector to expose the textbook recursion.
  simp [pocsOrbit, Function.iterate_succ_apply']

/-- A limiting POCS cycle is a family of points lying in the constraint sets, linked by the cyclic
projector relations, and realized as the weak limits of the corresponding shadow sequences. -/
structure IsPocsLimitCycle {m : ℕ} (C : Fin (m + 1) → Set H)
    (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) (x₀ : H) (y : Fin (m + 1) → H) : Prop where
  mem : ∀ i, y i ∈ C i
  projector_eq : ∀ i,
    y i =
      pocsProjectorFamily C hC_nonempty hC_closed hC_convex i (y (cyclicNext i))
  tendsto_shadow : ∀ i,
    Tendsto
      (fun n ↦
        toWeakSpace ℝ H
          (((cyclicShadow
              (liftUnivFamily (pocsProjectorFamily C hC_nonempty hC_closed hC_convex)) i)
              (((finiteComposition
                (liftUnivFamily (pocsProjectorFamily C hC_nonempty hC_closed hC_convex)))^[n])
                ⟨x₀, Set.mem_univ _⟩) : H_univ) : H))
      atTop (𝓝 (toWeakSpace ℝ H (y i)))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 5.24: the lifted family coerces back to the original ambient self-maps. -/
@[simp] private theorem liftUnivFamily_coe {m : ℕ} (T : Fin m → H → H) (i : Fin m)
    (x : H_univ) :
    ((liftUnivFamily T i x : H_univ) : H) = T i (x : H) :=
  rfl

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 5.24: lifting a finite ordered composition to `Set.univ` preserves its
ambient value after coercion. -/
@[simp] private theorem finiteComposition_liftUnivFamily_coe :
    {m : ℕ} → (T : Fin m → H → H) → ∀ x : H_univ,
      ((finiteComposition (liftUnivFamily T) x : H_univ) : H) = finiteComposition T (x : H)
  | 0, _, _ => rfl
  | _ + 1, T, x => by
      -- Expand the head-tail composition on both sides and rewrite the lifted tail recursively.
      rw [finiteComposition_succ, finiteComposition_succ]
      simp only [Function.comp_apply, liftUnivFamily_coe]
      exact congrArg (T 0)
        (finiteComposition_liftUnivFamily_coe (T := fun i ↦ T i.succ) (x := x))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 5.24: iterating the lifted ordered composition on `Set.univ` matches the
ambient iterate after coercion. -/
@[simp] private theorem iterate_finiteComposition_liftUnivFamily_coe {m : ℕ}
    (T : Fin m → H → H) (x : H_univ) :
    ∀ n, ((((finiteComposition (liftUnivFamily T))^[n]) x : H_univ) : H) =
      ((finiteComposition T)^[n]) (x : H)
  | 0 => rfl
  | n + 1 => by
      -- Push one more iterate through the coercion and then invoke the induction hypothesis.
      simp [Function.iterate_succ_apply', iterate_finiteComposition_liftUnivFamily_coe]

omit [CompleteSpace H] in
/-- Helper for Corollary 5.24: the reflected squared-norm gap expands to four times the firm
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

/-- Helper for Corollary 5.24: the POCS projector family lifts to self-maps of the whole-space
subtype needed by Theorem 5.23. -/
noncomputable abbrev pocsProjectorFamilyOnUniv {m : ℕ} (C : Fin (m + 1) → Set H)
    (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) :
    Fin (m + 1) → H_univ → H_univ :=
  liftUnivFamily (pocsProjectorFamily C hC_nonempty hC_closed hC_convex)

/-- Helper for Corollary 5.24: each metric projector in the POCS family is `1 / 2`-averaged on
`Set.univ`, exactly as required by Theorem 5.23. -/
theorem pocs_projectorFamily_averagedWith_half_on_univ {m : ℕ} (C : Fin (m + 1) → Set H)
    (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) (i : Fin (m + 1)) :
    AveragedWith (1 / 2 : ℝ)
      (fun x : H_univ ↦ ((pocsProjectorFamilyOnUniv C hC_nonempty hC_closed hC_convex i x :
        H_univ) : H)) := by
  let P : H_univ → H := fun x ↦
    ((pocsProjectorFamilyOnUniv C hC_nonempty hC_closed hC_convex i x : H_univ) : H)
  let R : H_univ → H := fun x ↦ (2 : ℝ) • P x - (x : H)
  refine averagedWith_iff.mpr ?_
  refine ⟨by norm_num, R, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    let a : H := (x : H) - y
    let b : H := P x - P y
    have hfirm :
        ‖b‖ ^ 2 ≤ inner ℝ a b := by
      -- Proposition 4.16 supplies the firm nonexpansiveness estimate for the metric projector.
      simpa [P, a, b, pocsProjectorFamilyOnUniv, pocsProjectorFamily, real_inner_comm] using
        norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
          (hC_nonempty i) (hC_closed i) (hC_convex i) (x : H) (y : H)
    have hsq :
        ‖(2 : ℝ) • b - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      -- The reflected gap identity turns the firm estimate into the required square bound.
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
    -- The chosen reflected companion realizes the standard `(Id + R) / 2` decomposition.
    dsimp [R, P]
    have hhalf_eq : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    calc
      (((pocsProjectorFamilyOnUniv C hC_nonempty hC_closed hC_convex i x : H_univ) : H))
          = (1 / 2 : ℝ) •
              ((2 : ℝ) •
                (((pocsProjectorFamilyOnUniv C hC_nonempty hC_closed hC_convex i x : H_univ) :
                  H))) := by
              rw [smul_smul]
              norm_num
      _ = (1 / 2 : ℝ) • (x : H) +
            ((1 / 2 : ℝ) •
              ((2 : ℝ) •
                (((pocsProjectorFamilyOnUniv C hC_nonempty hC_closed hC_convex i x : H_univ) :
                  H))) -
              (1 / 2 : ℝ) • (x : H)) := by
            abel_nf
      _ = (1 - (1 / 2 : ℝ)) • (x : H) + (1 / 2 : ℝ) • R x := by
            rw [hhalf_eq, smul_sub]

/-- Helper for Corollary 5.24: an ambient fixed point of the composite POCS operator yields a fixed
point of the lifted finite composition on `Set.univ`. -/
theorem fixedPoint_finiteComposition_pocsProjectorFamily_on_univ {m : ℕ}
    (C : Fin (m + 1) → Set H) (hC_nonempty : ∀ i, (C i).Nonempty)
    (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i))
    (hfix :
      (Function.fixedPoints (pocsOperator C hC_nonempty hC_closed hC_convex)).Nonempty) :
    (Function.fixedPoints
      (finiteComposition
        (pocsProjectorFamilyOnUniv C hC_nonempty hC_closed hC_convex))).Nonempty := by
  rcases hfix with ⟨z, hz⟩
  refine ⟨⟨z, Set.mem_univ _⟩, ?_⟩
  rw [Function.mem_fixedPoints_iff] at hz ⊢
  -- Coerce the lifted fixed-point equation back to the ambient space and reuse the given witness.
  apply Subtype.ext
  simpa [pocsOperator, pocsProjectorFamilyOnUniv] using hz

/-- Helper for Corollary 5.24: cyclic weak-limit data for the lifted projector family on `Set.univ`
packages into the ambient `IsPocsLimitCycle` structure. -/
theorem isPocsLimitCycle_of_cyclicWeakLimits_univ {m : ℕ} (C : Fin (m + 1) → Set H)
    (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) (x₀ : H) {y : Fin (m + 1) → H_univ}
    (hshadow :
      ∀ i : Fin (m + 1),
        Tendsto
          (fun k ↦ toWeakSpace ℝ H
            (((cyclicShadow (pocsProjectorFamilyOnUniv C hC_nonempty hC_closed hC_convex) i)
              (((finiteComposition
                (pocsProjectorFamilyOnUniv C hC_nonempty hC_closed hC_convex))^[k])
                ⟨x₀, Set.mem_univ _⟩) : H_univ) : H))
          atTop (𝓝 (toWeakSpace ℝ H (y i : H))))
    (hcycle :
      ∀ i : Fin (m + 1),
        y i =
          pocsProjectorFamilyOnUniv C hC_nonempty hC_closed hC_convex i (y (cyclicNext i))) :
    IsPocsLimitCycle C hC_nonempty hC_closed hC_convex x₀ (fun i ↦ (y i : H)) := by
  have hprojector_eq :
      ∀ i : Fin (m + 1),
        (y i : H) =
          pocsProjectorFamily C hC_nonempty hC_closed hC_convex i (y (cyclicNext i)) := by
    intro i
    -- Coerce the cyclic relation from the subtype output of Theorem 5.23 back to the ambient space.
    simpa [pocsProjectorFamilyOnUniv] using
      congrArg (fun z : H_univ ↦ (z : H)) (hcycle i)
  refine
    { mem := ?_
      projector_eq := hprojector_eq
      tendsto_shadow := ?_ }
  · intro i
    -- The projector relation lands in `C i`, so membership follows from the metric projection API.
    rw [hprojector_eq i]
    exact
      projectionPoint_mem (C i)
        (isChebyshev_of_nonempty_isClosed_convex (hC_nonempty i) (hC_closed i) (hC_convex i))
        (y (cyclicNext i) : H)
  · intro i
    -- The limit data already uses the lifted projector family on `Set.univ`.
    simpa [pocsProjectorFamilyOnUniv] using hshadow i

-- Proof sketch: apply Theorem 5.23 to the finite family of metric projectors attached to the
-- sets `C i`; Proposition 4.16 identifies each projector as firmly nonexpansive, and the fixed
-- point hypothesis on their ordered composition supplies the assumption required to obtain a weak
-- limiting cycle for the POCS orbit and all of its shadow sequences.
/-- Corollary 5.24: if a finite cyclic family of nonempty closed convex sets in a real Hilbert
space has a composite projector with a fixed point, then the POCS orbit starting from `x₀` admits
points `y₁, …, y_m` in the respective sets that form a cyclic projector relation and are the weak
limits of the orbit and its tail-shadow sequences. -/
theorem exists_pocs_limitCycle_of_fixedPoint_pocsOperator {m : ℕ}
    (C : Fin (m + 1) → Set H) (hC_nonempty : ∀ i, (C i).Nonempty)
    (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i)) (x₀ : H)
    (hfix :
      (Function.fixedPoints (pocsOperator C hC_nonempty hC_closed hC_convex)).Nonempty) :
    ∃ y, IsPocsLimitCycle C hC_nonempty hC_closed hC_convex x₀ y := by
  let T : Fin (m + 1) → H_univ → H_univ :=
    pocsProjectorFamilyOnUniv C hC_nonempty hC_closed hC_convex
  let x₀_univ : H_univ := ⟨x₀, Set.mem_univ _⟩
  have hAveraged :
      ∀ i : Fin (m + 1), ∃ α : ℝ, AveragedWith α (fun x : H_univ ↦ (T i x : H)) := by
    intro i
    -- Each projector is `1 / 2`-averaged, so Theorem 5.23 applies directly on `Set.univ`.
    refine ⟨1 / 2, ?_⟩
    simpa [T] using
      pocs_projectorFamily_averagedWith_half_on_univ C hC_nonempty hC_closed hC_convex i
  have hFix_univ :
      (Function.fixedPoints (finiteComposition T)).Nonempty :=
    fixedPoint_finiteComposition_pocsProjectorFamily_on_univ C hC_nonempty hC_closed hC_convex
      hfix
  rcases
      (residual_tendsto_zero_and_exists_cyclicWeakLimits_of_averaged_finiteComposition
        (D := H_univ) (hD_closed := by simp)
        (hD_convex := by simpa using (convex_univ : Convex ℝ H_univ)) T hAveraged hFix_univ
        x₀_univ).2 with
    ⟨y, hshadow, hcycle, _⟩
  -- Package the weak-limit cycle returned by Theorem 5.23 into the ambient POCS cycle structure.
  refine ⟨fun i ↦ (y i : H), ?_⟩
  exact isPocsLimitCycle_of_cyclicWeakLimits_univ C hC_nonempty hC_closed hC_convex x₀
    hshadow hcycle

end
