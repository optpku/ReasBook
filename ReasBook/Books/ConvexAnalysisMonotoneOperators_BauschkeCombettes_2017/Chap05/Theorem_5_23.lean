/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {D : Set H}

/- The cyclic successor on `Fin (n + 1)`, sending the last index back to `0`. -/
def cyclicNext {n : ℕ} : Fin (n + 1) → Fin (n + 1) :=
  Fin.lastCases 0 Fin.succ

private def suffixComposition {α : Type*} : {m : ℕ} → (Fin m → α → α) → Fin m → α → α
  | 0, _, i => Fin.elim0 i
  | _ + 1, T, ⟨0, _⟩ => finiteComposition T
  | _ + 1, T, ⟨k + 1, hk⟩ =>
      suffixComposition (fun i ↦ T i.succ) ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- The shadow operators of a cyclic family: `0` gives the identity and `i.succ` gives the suffix
composition beginning with `T i.succ`. -/
def cyclicShadow {α : Type*} : {m : ℕ} → (Fin m → α → α) → Fin m → α → α
  | 0, _, i => Fin.elim0 i
  | _ + 1, _, ⟨0, _⟩ => id
  | _ + 1, T, ⟨k + 1, hk⟩ =>
      suffixComposition (fun i ↦ T i.succ) ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- The cyclic composition obtained by starting the ordered finite composition at the index `i`
and then wrapping around modulo the family length. -/
def cyclicComposition {α : Type*} {m : ℕ} (T : Fin m → α → α) (i : Fin m) : α → α :=
  finiteComposition (fun j ↦ T (j + i))

/-- Helper for Theorem 5.23: the cyclic successor is addition by `1` in `Fin (n + 1)`. -/
private theorem cyclicNext_eq_add_one {n : ℕ} (i : Fin (n + 1)) :
    cyclicNext i = i + 1 := by
  -- Split into the wrap-around case and the ordinary successor case.
  cases i using Fin.lastCases with
  | last =>
      apply Fin.ext
      simp [cyclicNext]
  | cast j =>
      apply Fin.ext
      simp [cyclicNext]

/-- Helper for Theorem 5.23: moving one step earlier in a suffix composition peels off the head
map of the remaining tail. -/
private theorem suffixComposition_castSucc_apply {α : Type*} :
    ∀ {n : ℕ} (T : Fin (n + 1) → α → α) (i : Fin n) (x : α),
      suffixComposition T i.castSucc x = T i.castSucc (suffixComposition T i.succ x)
  | 0, T, i, x => Fin.elim0 i
  | _ + 1, T, i, x => by
      cases i using Fin.cases with
      | zero =>
          -- At the head index, the suffix composition is the full ordered composition.
          change finiteComposition T x = T 0 (suffixComposition T 1 x)
          rw [finiteComposition_succ]
          rfl
      | succ j =>
          -- Away from the head, both sides recurse on the tail family.
          simpa [suffixComposition] using
            suffixComposition_castSucc_apply (T := fun k ↦ T k.succ) (i := j) (x := x)

/-- Helper for Theorem 5.23: the last suffix composition is just the last map in the family. -/
private theorem suffixComposition_last_apply {α : Type*} :
    ∀ {n : ℕ} (T : Fin (n + 1) → α → α) (x : α),
      suffixComposition T (Fin.last n) x = T (Fin.last n) x
  | 0, T, x => by
      -- For a singleton family, the full composition is the only map.
      change finiteComposition T x = T 0 x
      rfl
  | _ + 1, T, x => by
      -- The recursive definition reduces the last index to the last index of the tail family.
      simpa [suffixComposition] using
        suffixComposition_last_apply (T := fun k ↦ T k.succ) (x := x)

/-- Helper for Theorem 5.23: a cyclic family relation transports the base point `y 0` to every
suffix output. -/
private theorem suffixComposition_apply_eq_cyclePoint {α : Type*} {n : ℕ}
    (T : Fin (n + 1) → α → α) (y : Fin (n + 1) → α)
    (hcycle : ∀ i : Fin (n + 1), y i = T i (y (cyclicNext i))) :
    ∀ j : Fin (n + 1), suffixComposition T j (y 0) = y j := by
  refine Fin.reverseInduction ?_ ?_
  · -- At the last index, the cyclic relation closes the loop back to `0`.
    rw [suffixComposition_last_apply]
    simpa [cyclicNext_eq_add_one] using (hcycle (Fin.last n)).symm
  · intro i ih
    -- One reverse-induction step peels off the current head map and uses the cycle relation.
    calc
      suffixComposition T i.castSucc (y 0) = T i.castSucc (suffixComposition T i.succ (y 0)) := by
        rw [suffixComposition_castSucc_apply]
      _ = T i.castSucc (y i.succ) := by
        rw [ih]
      _ = y i.castSucc := by
        simpa [cyclicNext_eq_add_one] using (hcycle i.castSucc).symm

/-- The cyclic relations from Theorem 5.23 imply that each limit point is a fixed point of the
corresponding cyclic composition. -/
theorem mem_fixedPoints_cyclicComposition_of_cycle_eq {n : ℕ} (T : Fin (n + 1) → D → D)
    {y : Fin (n + 1) → D} (hcycle : ∀ i : Fin (n + 1), y i = T i (y (cyclicNext i)))
    (i : Fin (n + 1)) :
    y i ∈ fixedPoints (cyclicComposition T i) := by
  rw [Function.mem_fixedPoints_iff]
  let S : Fin (n + 1) → D → D := fun j ↦ T (j + i)
  let z : Fin (n + 1) → D := fun j ↦ y (j + i)
  have hcycle' : ∀ j : Fin (n + 1), z j = S j (z (cyclicNext j)) := by
    intro j
    -- Reindex the original cyclic relations by the starting index `i`.
    change y (j + i) = T (j + i) (y (cyclicNext j + i))
    simpa [cyclicNext_eq_add_one, add_assoc, add_left_comm, add_comm] using hcycle (j + i)
  -- The shifted family satisfies the same cycle relation, so its full composition fixes `z 0`.
  simpa [cyclicComposition, S, z, add_comm] using
    suffixComposition_apply_eq_cyclePoint S z hcycle' 0

/-- Helper for Theorem 5.23: every positive cyclic shadow is obtained by applying the
corresponding map to the next shadow. -/
private theorem cyclicShadow_succ_apply {α : Type*} :
    ∀ {n : ℕ} (T : Fin (n + 1) → α → α) (i : Fin n) (x : α),
      cyclicShadow T i.succ x = T i.succ (cyclicShadow T (cyclicNext i.succ) x)
  | 0, T, i, x => Fin.elim0 i
  | n + 1, T, i, x => by
      let U : Fin (n + 1) → α → α := fun j ↦ T j.succ
      cases i using Fin.lastCases with
      | last =>
          -- At the last positive index, the next shadow wraps back to `0`, so the suffix collapses
          -- to the last operator itself.
          have hnext : cyclicNext ((Fin.last n).succ : Fin (n + 2)) = (0 : Fin (n + 2)) := by
            apply Fin.ext
            simp [cyclicNext_eq_add_one, Fin.succ_last]
          calc
            cyclicShadow T ((Fin.last n).succ) x = suffixComposition U (Fin.last n) x := by
              rfl
            _ = U (Fin.last n) x := by
              rw [suffixComposition_last_apply]
            _ = T ((Fin.last n).succ) x := by
              rfl
            _ = T ((Fin.last n).succ) (cyclicShadow T (cyclicNext ((Fin.last n).succ)) x) := by
              rw [hnext]
              rfl
      | cast j =>
          -- Away from the end of the cycle, the next shadow is the tail suffix one step later.
          have hnext : cyclicNext (j.castSucc.succ : Fin (n + 2)) = j.succ.succ := by
            rw [cyclicNext_eq_add_one]
            apply Fin.ext
            rw [Fin.val_add_one_of_lt]
            · simp [Fin.val_succ]
            · rw [Fin.lt_def, Fin.val_succ, Fin.val_last]
              exact Nat.succ_lt_succ j.isLt
          calc
            cyclicShadow T j.castSucc.succ x = suffixComposition U j.castSucc x := by
              rfl
            _ = U j.castSucc (suffixComposition U j.succ x) := by
              rw [suffixComposition_castSucc_apply]
            _ = T j.castSucc.succ (suffixComposition U j.succ x) := by
              rfl
            _ = T j.castSucc.succ (cyclicShadow T (cyclicNext j.castSucc.succ) x) := by
              rw [hnext]
              rfl

/-- Helper for Theorem 5.23: a fixed point of the ordered composition satisfies the full cyclic
shadow relations. -/
private theorem cyclicShadow_cycle_eq_of_mem_fixedPoints {n : ℕ}
    (T : Fin (n + 1) → D → D) {z : D} (hz : z ∈ fixedPoints (finiteComposition T)) :
    ∀ i : Fin (n + 1), cyclicShadow T i z = T i (cyclicShadow T (cyclicNext i) z) := by
  intro i
  cases i using Fin.cases with
  | zero =>
      rw [Function.mem_fixedPoints_iff] at hz
      -- The `i = 0` relation is exactly the fixed-point equation of the full composition.
      calc
        cyclicShadow T 0 z = z := rfl
        _ = finiteComposition T z := hz.symm
        _ = T 0 (finiteComposition (fun j ↦ T j.succ) z) := by
              rfl
        _ = T 0 (cyclicShadow T (cyclicNext 0) z) := by
              cases n with
              | zero =>
                  have hnext : cyclicNext (0 : Fin 1) = 0 := by
                    rfl
                  rw [hnext]
                  rfl
              | succ n =>
                  have hnext : cyclicNext (0 : Fin (n + 2)) = 1 := by
                    apply Fin.ext
                    simp [cyclicNext_eq_add_one]
                  rw [hnext]
                  rfl
  | succ j =>
      -- Every positive shadow is definitionally the corresponding tail map applied to the next
      -- shadow in the cycle.
      simpa using cyclicShadow_succ_apply (T := T) (i := j) (x := z)

/-- Helper for Theorem 5.23: the cyclic shadow family of a fixed point of the ordered composition
consists of fixed points of all cyclic rotations. -/
private theorem cyclicShadow_mem_fixedPoints_cyclicComposition_of_mem_fixedPoints {n : ℕ}
    (T : Fin (n + 1) → D → D) {z : D} (hz : z ∈ fixedPoints (finiteComposition T))
    (i : Fin (n + 1)) :
    cyclicShadow T i z ∈ fixedPoints (cyclicComposition T i) := by
  let y : Fin (n + 1) → D := fun j ↦ cyclicShadow T j z
  have hcycle : ∀ j : Fin (n + 1), y j = T j (y (cyclicNext j)) := by
    intro j
    -- Package the shadow cycle relation into the form expected by the cyclic fixed-point bridge.
    simpa [y] using cyclicShadow_cycle_eq_of_mem_fixedPoints (T := T) hz j
  -- The previously established cyclic fixed-point bridge applies directly to the shadow family.
  simpa [y] using mem_fixedPoints_cyclicComposition_of_cycle_eq T hcycle i

/-- Helper for Theorem 5.23: after removing the head map of a nonempty family, the successor
shadow in the original family becomes the corresponding cyclic-next shadow in the tail family. -/
private theorem cyclicShadow_cyclicNext_succ_eq_tail {α : Type*} :
    ∀ {n : ℕ} (T : Fin (n + 2) → α → α) (i : Fin (n + 1)) (x : α),
      cyclicShadow T (cyclicNext i.succ) x =
        cyclicShadow (fun j : Fin (n + 1) ↦ T j.succ) (cyclicNext i) x
  | n, T, i, x => by
      cases i using Fin.lastCases with
      | last =>
          -- At the end of the cycle, both cyclic successors wrap to the identity shadow.
          have hnextT : cyclicNext ((Fin.last n).succ : Fin (n + 2)) = (0 : Fin (n + 2)) := by
            apply Fin.ext
            simp [cyclicNext_eq_add_one, Fin.succ_last]
          have hnextU : cyclicNext (Fin.last n : Fin (n + 1)) = (0 : Fin (n + 1)) := by
            apply Fin.ext
            simp [cyclicNext_eq_add_one]
          rw [hnextT, hnextU]
          rfl
      | cast j =>
          -- Away from the end, both shadows recurse on the same tail family.
          have hnextT : cyclicNext (j.castSucc.succ : Fin (n + 2)) = j.succ.succ := by
            rw [cyclicNext_eq_add_one]
            apply Fin.ext
            rw [Fin.val_add_one_of_lt]
            · simp [Fin.val_succ]
            · rw [Fin.lt_def, Fin.val_succ, Fin.val_last]
              exact Nat.succ_lt_succ j.isLt
          have hnextU : cyclicNext (j.castSucc : Fin (n + 1)) = j.succ := by
            rw [cyclicNext_eq_add_one]
            apply Fin.ext
            rw [Fin.val_add_one_of_lt]
            · simp [Fin.val_succ]
            · rw [Fin.lt_def, Fin.val_last]
              exact j.isLt
          rw [hnextT, hnextU]
          rfl

/-- Helper for Theorem 5.23: the cyclic-shadow defect vectors telescope to the Picard residual
of the ordered finite composition. -/
private theorem cyclicShadow_defect_sum_eq_picard_residual {n : ℕ}
    (T : Fin (n + 1) → D → D) (z : D) :
    (∑ i : Fin (n + 1),
      (((cyclicShadow T (cyclicNext i) z : D) : H) -
        ((T i (cyclicShadow T (cyclicNext i) z) : D) : H))) =
      (z : H) - ((finiteComposition T z : D) : H) := by
  induction n with
  | zero =>
      -- For a singleton family, the only defect is exactly the residual `z - T 0 z`.
      have hnext : cyclicNext (0 : Fin 1) = (0 : Fin 1) := rfl
      simp [hnext, cyclicShadow, finiteComposition]
  | succ n ih =>
      let U : Fin (n + 1) → D → D := fun i ↦ T i.succ
      let δ : Fin (n + 2) → H := fun i ↦
        ((cyclicShadow T (cyclicNext i) z : D) : H) -
          ((T i (cyclicShadow T (cyclicNext i) z) : D) : H)
      let δtail : Fin (n + 1) → H := fun i ↦
        ((cyclicShadow U (cyclicNext i) z : D) : H) -
          ((U i (cyclicShadow U (cyclicNext i) z) : D) : H)
      have hzero :
          δ 0 = ((finiteComposition U z : D) : H) - ((T 0 (finiteComposition U z) : D) : H) := by
        -- The head defect is the first residual term of the ordered composition.
        have hnext : cyclicNext (0 : Fin (n + 2)) = (1 : Fin (n + 2)) := by
          apply Fin.ext
          simp [cyclicNext_eq_add_one]
        dsimp [δ]
        rw [hnext]
        rfl
      have hsucc :
          ∀ i : Fin (n + 1), δ i.succ = δtail i := by
        intro i
        -- Every successor defect is exactly the corresponding tail-family defect.
        simp [δ, δtail, U, cyclicShadow_cyclicNext_succ_eq_tail (T := T) (i := i) (x := z)]
      have htail :
          ∑ i : Fin (n + 1), δ i.succ = (z : H) - ((finiteComposition U z : D) : H) := by
        -- Apply the induction hypothesis after identifying the successor defects with the tail
        -- defects.
        calc
          ∑ i : Fin (n + 1), δ i.succ = ∑ i : Fin (n + 1), δtail i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hsucc i
          _ = (z : H) - ((finiteComposition U z : D) : H) := ih U
      -- Split the finite sum into the head defect and the tail defects, then telescope.
      calc
        ∑ i : Fin (n + 2), δ i = δ 0 + ∑ i : Fin (n + 1), δ i.succ := by
          simpa using (Fin.sum_univ_succ δ)
        _ = ((finiteComposition U z : D) : H) - ((T 0 (finiteComposition U z) : D) : H) +
              ((z : H) - ((finiteComposition U z : D) : H)) := by
                rw [hzero, htail]
        _ = (z : H) - ((T 0 (finiteComposition U z) : D) : H) := by
          abel_nf
        _ = (z : H) - ((finiteComposition T z : D) : H) := by
          rfl

/-- Helper for Theorem 5.23: each averaged factor contributes its Proposition 4.35
residual-squared-norm estimate at the corresponding cyclic-shadow inputs. -/
private theorem cyclicShadow_residual_sqnorm_step {n : ℕ}
    (T : Fin (n + 1) → D → D)
    (hAveraged : ∀ i, ∃ α : ℝ, AveragedWith α (fun x : D ↦ (T i x : H)))
    (i : Fin (n + 1)) (x y : D) :
    ∃ α : ℝ,
      α ∈ Set.Ioo (0 : ℝ) 1 ∧
        ‖((T i (cyclicShadow T (cyclicNext i) x) : D) : H) -
            ((T i (cyclicShadow T (cyclicNext i) y) : D) : H)‖ ^ 2 ≤
          ‖((cyclicShadow T (cyclicNext i) x : D) : H) -
              ((cyclicShadow T (cyclicNext i) y : D) : H)‖ ^ 2 -
            ((1 - α) / α) *
              ‖((((cyclicShadow T (cyclicNext i) x : D) : H) -
                    ((T i (cyclicShadow T (cyclicNext i) x) : D) : H))) -
                  ((((cyclicShadow T (cyclicNext i) y : D) : H) -
                    ((T i (cyclicShadow T (cyclicNext i) y) : D) : H)))‖ ^ 2 := by
  rcases hAveraged i with ⟨α, hα⟩
  have hαIoo : α ∈ Set.Ioo (0 : ℝ) 1 := hα.mem_Ioo
  refine ⟨α, hαIoo, ?_⟩
  -- Proposition 4.35 applies directly once the consecutive shadows are chosen as the two inputs.
  simpa using
    ((averagedWith_iff_residual_sqnorm_ineq hαIoo).1 hα
      (cyclicShadow T (cyclicNext i) x) (cyclicShadow T (cyclicNext i) y))

/-- Helper for Theorem 5.23: every averaged self-map is nonexpansive. -/
private theorem lipschitzWith_one_of_averagedWith_local {α : ℝ} {T : D → H}
    (hT : AveragedWith α T) : LipschitzWith 1 T := by
  rcases averagedWith_iff.mp hT with ⟨hα, R, hR, hT_eq⟩
  have hα_nonneg : 0 ≤ α := hα.1.le
  have h_one_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
  -- Expand the averaged representation and compare the companion map with its nonexpansive
  -- witness.
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hRxy : ‖R x - R y‖ ≤ ‖(x : H) - y‖ := by
    simpa [Subtype.dist_eq, dist_eq_norm] using hR.dist_le_mul x y
  have hxy :
      T x - T y = (1 - α) • ((x : H) - y) + α • (R x - R y) := by
    calc
      T x - T y
          = ((1 - α) • (x : H) + α • R x) - ((1 - α) • (y : H) + α • R y) := by
              rw [hT_eq]
      _ = (1 - α) • ((x : H) - y) + α • (R x - R y) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using
    calc
      ‖T x - T y‖ = ‖(1 - α) • ((x : H) - y) + α • (R x - R y)‖ := by
        rw [hxy]
      _ ≤ ‖(1 - α) • ((x : H) - y)‖ + ‖α • (R x - R y)‖ := norm_add_le _ _
      _ = (1 - α) * ‖(x : H) - y‖ + α * ‖R x - R y‖ := by
            rw [norm_smul, norm_smul]
            simp [Real.norm_eq_abs, abs_of_nonneg h_one_sub_nonneg, abs_of_nonneg hα_nonneg]
      _ ≤ (1 - α) * ‖(x : H) - y‖ + α * ‖(x : H) - y‖ := by
            nlinarith [hRxy, norm_nonneg ((x : H) - y)]
      _ = ‖(x : H) - y‖ := by
            ring

/-- Helper for Theorem 5.23: the ordered finite composition is nonexpansive because each averaged
factor is nonexpansive and finite compositions preserve the Lipschitz constant `1`. -/
private theorem lipschitzWith_one_finiteComposition_of_averaged {n : ℕ}
    (T : Fin (n + 1) → D → D)
    (hAveraged : ∀ i, ∃ α : ℝ, AveragedWith α (fun x : D ↦ (T i x : H))) :
    LipschitzWith 1 (finiteComposition T) := by
  -- Remark 4.34 upgrades each averaged factor to a nonexpansive map.
  refine lipschitzWith_finiteComposition T ?_
  intro i
  rcases hAveraged i with ⟨α, hα⟩
  exact lipschitzWith_one_of_averagedWith_local hα

/-- Helper for Theorem 5.23: iterating the Proposition 4.35 estimate along the ordered finite
composition produces the full cyclic-shadow defect-chain inequality. -/
private theorem finiteComposition_sqnorm_drop_ge_cyclicShadow_defect_sum {n : ℕ}
    (T : Fin (n + 1) → D → D) (α : Fin (n + 1) → ℝ)
    (hαIoo : ∀ i, α i ∈ Set.Ioo (0 : ℝ) 1)
    (hAveraged : ∀ i, AveragedWith (α i) (fun x : D ↦ (T i x : H)))
    (x z : D) :
    ‖((finiteComposition T x : D) : H) - ((finiteComposition T z : D) : H)‖ ^ 2 ≤
      ‖(x : H) - z‖ ^ 2 -
        ∑ i : Fin (n + 1),
          ((1 - α i) / α i) *
            ‖((((cyclicShadow T (cyclicNext i) x : D) : H) -
                  ((T i (cyclicShadow T (cyclicNext i) x) : D) : H))) -
                ((((cyclicShadow T (cyclicNext i) z : D) : H) -
                  ((T i (cyclicShadow T (cyclicNext i) z) : D) : H)))‖ ^ 2 := by
  induction n with
  | zero =>
      -- For a singleton family, the whole claim is exactly Proposition 4.35.
      have hstep :=
        ((averagedWith_iff_residual_sqnorm_ineq (hαIoo 0)).1 (hAveraged 0)) x z
      have hnext : cyclicNext (0 : Fin 1) = 0 := rfl
      simpa [finiteComposition, cyclicShadow, hnext] using hstep
  | succ n ih =>
      let U : Fin (n + 1) → D → D := fun i ↦ T i.succ
      let defectSq : Fin (n + 2) → ℝ := fun i ↦
        ((1 - α i) / α i) *
          ‖((((cyclicShadow T (cyclicNext i) x : D) : H) -
                ((T i (cyclicShadow T (cyclicNext i) x) : D) : H))) -
              ((((cyclicShadow T (cyclicNext i) z : D) : H) -
                ((T i (cyclicShadow T (cyclicNext i) z) : D) : H)))‖ ^ 2
      let defectSqTail : Fin (n + 1) → ℝ := fun i ↦
        ((1 - α i.succ) / α i.succ) *
          ‖((((cyclicShadow U (cyclicNext i) x : D) : H) -
                ((U i (cyclicShadow U (cyclicNext i) x) : D) : H))) -
              ((((cyclicShadow U (cyclicNext i) z : D) : H) -
                ((U i (cyclicShadow U (cyclicNext i) z) : D) : H)))‖ ^ 2
      have hhead :
          ‖((finiteComposition T x : D) : H) - ((finiteComposition T z : D) : H)‖ ^ 2 ≤
            ‖((finiteComposition U x : D) : H) - ((finiteComposition U z : D) : H)‖ ^ 2 -
              ((1 - α 0) / α 0) *
                ‖((((finiteComposition U x : D) : H) -
                      ((finiteComposition T x : D) : H))) -
                    ((((finiteComposition U z : D) : H) -
                      ((finiteComposition T z : D) : H)))‖ ^ 2 := by
        -- The head factor contributes the first defect term after the tail composition.
        simpa [finiteComposition_succ, U] using
          ((averagedWith_iff_residual_sqnorm_ineq (hαIoo 0)).1 (hAveraged 0))
            (finiteComposition U x) (finiteComposition U z)
      have htail :
          ‖((finiteComposition U x : D) : H) - ((finiteComposition U z : D) : H)‖ ^ 2 ≤
            ‖(x : H) - z‖ ^ 2 - ∑ i : Fin (n + 1), defectSqTail i := by
        -- Apply the induction hypothesis to the tail family.
        simpa [U, defectSqTail] using
          ih U (fun i ↦ α i.succ) (fun i ↦ hαIoo i.succ) (fun i ↦ hAveraged i.succ)
      have hdefect_zero :
          defectSq 0 =
            ((1 - α 0) / α 0) *
              ‖((((finiteComposition U x : D) : H) -
                    ((finiteComposition T x : D) : H))) -
                  ((((finiteComposition U z : D) : H) -
                    ((finiteComposition T z : D) : H)))‖ ^ 2 := by
        -- The shadow after the first cyclic successor is exactly the tail composition.
        have hnext : cyclicNext (0 : Fin (n + 2)) = (1 : Fin (n + 2)) := by
          apply Fin.ext
          simp [cyclicNext_eq_add_one]
        dsimp [defectSq]
        rw [hnext]
        rfl
      have hdefect_succ :
          ∀ i : Fin (n + 1), defectSq i.succ = defectSqTail i := by
        intro i
        -- Successor defects are exactly the tail-family defects.
        simp [defectSq, defectSqTail, U, cyclicShadow_cyclicNext_succ_eq_tail (T := T) (i := i)
          (x := x), cyclicShadow_cyclicNext_succ_eq_tail (T := T) (i := i) (x := z)]
      have hsum :
          defectSq 0 + ∑ i : Fin (n + 1), defectSqTail i = ∑ i : Fin (n + 2), defectSq i := by
        calc
          defectSq 0 + ∑ i : Fin (n + 1), defectSqTail i
              = defectSq 0 + ∑ i : Fin (n + 1), defectSq i.succ := by
                  refine congrArg (fun t ↦ defectSq 0 + t) ?_
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  exact (hdefect_succ i).symm
          _ = ∑ i : Fin (n + 2), defectSq i := by
                symm
                simpa using (Fin.sum_univ_succ defectSq)
      -- Chain the head estimate with the tail estimate and repackage the full weighted sum.
      calc
        ‖((finiteComposition T x : D) : H) - ((finiteComposition T z : D) : H)‖ ^ 2
            ≤ ‖((finiteComposition U x : D) : H) - ((finiteComposition U z : D) : H)‖ ^ 2 -
                defectSq 0 := by
                  simpa [hdefect_zero] using hhead
        _ ≤ (‖(x : H) - z‖ ^ 2 - ∑ i : Fin (n + 1), defectSqTail i) - defectSq 0 := by
              gcongr
        _ = ‖(x : H) - z‖ ^ 2 - (defectSq 0 + ∑ i : Fin (n + 1), defectSqTail i) := by
              ring
        _ = ‖(x : H) - z‖ ^ 2 - ∑ i : Fin (n + 2), defectSq i := by
              rw [hsum]

/-- Helper for Theorem 5.23: along the Picard orbit of the ordered composition, every
cyclic-shadow defect converges strongly to the corresponding defect at a fixed point. -/
private theorem cyclicShadow_defect_tendsto_zero_of_picard_orbit {n : ℕ}
    (T : Fin (n + 1) → D → D) (α : Fin (n + 1) → ℝ)
    (hαIoo : ∀ i, α i ∈ Set.Ioo (0 : ℝ) 1)
    (hAveraged : ∀ i, AveragedWith (α i) (fun x : D ↦ (T i x : H)))
    (x₀ : D) {z : D} (hz : z ∈ fixedPoints (finiteComposition T))
    (i : Fin (n + 1)) :
    let S : D → D := finiteComposition T
    let xk : ℕ → D := fun k ↦ (S^[k]) x₀
    Tendsto
      (fun k ↦
        ((((cyclicShadow T (cyclicNext i) (xk k) : D) : H) -
              ((T i (cyclicShadow T (cyclicNext i) (xk k)) : D) : H))) -
            ((((cyclicShadow T (cyclicNext i) z : D) : H) -
              ((T i (cyclicShadow T (cyclicNext i) z) : D) : H))))
      atTop (𝓝 (0 : H)) := by
  let S : D → D := finiteComposition T
  let xk : ℕ → D := fun k ↦ (S^[k]) x₀
  let s : ℕ → ℝ := fun k ↦ ‖(xk k : H) - z‖ ^ 2
  let defect : Fin (n + 1) → ℕ → H := fun j k ↦
    ((((cyclicShadow T (cyclicNext j) (xk k) : D) : H) -
          ((T j (cyclicShadow T (cyclicNext j) (xk k)) : D) : H))) -
        ((((cyclicShadow T (cyclicNext j) z : D) : H) -
          ((T j (cyclicShadow T (cyclicNext j) z) : D) : H)))
  let defectWeight : Fin (n + 1) → ℕ → ℝ := fun j k ↦
    ((1 - α j) / α j) * ‖defect j k‖ ^ 2
  have hz_fixed : finiteComposition T z = z := Function.mem_fixedPoints_iff.mp hz
  have hdrop :
      ∀ k,
        s (k + 1) ≤
          s k - ∑ j : Fin (n + 1), defectWeight j k := by
    intro k
    -- Apply the full defect-chain inequality to the `k`th Picard iterate and the fixed point `z`.
    simpa [S, xk, s, defectWeight, defect, hz_fixed, Function.iterate_succ_apply'] using
      finiteComposition_sqnorm_drop_ge_cyclicShadow_defect_sum T α hαIoo hAveraged (xk k) z
  have hdefectWeight_nonneg :
      ∀ j : Fin (n + 1), ∀ k, 0 ≤ defectWeight j k := by
    intro j k
    have hβ_nonneg : 0 ≤ (1 - α j) / α j := by
      have hj := hαIoo j
      exact div_nonneg (sub_nonneg.mpr hj.2.le) hj.1.le
    exact mul_nonneg hβ_nonneg (sq_nonneg ‖defect j k‖)
  have hs_step : ∀ k, s (k + 1) ≤ s k := by
    intro k
    exact le_trans (hdrop k) <|
      sub_le_self _ (Finset.sum_nonneg fun j _ ↦ hdefectWeight_nonneg j k)
  have hs_antitone : Antitone s := antitone_nat_of_succ_le hs_step
  have hs_bddBelow : BddBelow (Set.range s) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact sq_nonneg ‖(xk k : H) - z‖
  let ℓ : ℝ := ⨅ k, s k
  have hℓ_tendsto : Tendsto s atTop (𝓝 ℓ) := by
    simpa [s, ℓ] using tendsto_atTop_ciInf hs_antitone hs_bddBelow
  have hdrop_tendsto_zero :
      Tendsto (fun k ↦ s k - s (k + 1)) atTop (𝓝 (0 : ℝ)) := by
    -- Successive drops of a convergent monotone sequence must vanish.
    simpa [s, ℓ, Nat.succ_eq_add_one] using
      hℓ_tendsto.sub (hℓ_tendsto.comp (tendsto_add_atTop_nat 1))
  have hweighted_le :
      ∀ k, defectWeight i k ≤ s k - s (k + 1) := by
    intro k
    have hsum_le : ∑ j : Fin (n + 1), defectWeight j k ≤ s k - s (k + 1) := by
      nlinarith [hdrop k]
    have hsingle :
        defectWeight i k ≤ ∑ j : Fin (n + 1), defectWeight j k := by
      simpa using
        (Finset.single_le_sum (fun j _ ↦ hdefectWeight_nonneg j k) (Finset.mem_univ i) :
          defectWeight i k ≤ ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))), defectWeight j k)
    exact le_trans hsingle hsum_le
  have hdefect_sq_le :
      ∀ k, ‖defect i k‖ ^ 2 ≤ (α i / (1 - α i)) * (s k - s (k + 1)) := by
    intro k
    have hi := hαIoo i
    have hscale_nonneg : 0 ≤ α i / (1 - α i) := by
      exact div_nonneg hi.1.le (sub_nonneg.mpr hi.2.le)
    have hcoeff :
        (α i / (1 - α i)) * ((1 - α i) / α i) = (1 : ℝ) := by
      rw [div_mul_div_comm, mul_comm]
      exact div_self (mul_ne_zero (sub_ne_zero.mpr (ne_of_lt hi.2).symm) hi.1.ne')
    have hrewrite :
        (α i / (1 - α i)) * defectWeight i k = ‖defect i k‖ ^ 2 := by
      calc
        (α i / (1 - α i)) * defectWeight i k
            = ((α i / (1 - α i)) * ((1 - α i) / α i)) * ‖defect i k‖ ^ 2 := by
                simp [defectWeight, mul_assoc, mul_left_comm, mul_comm]
        _ = ‖defect i k‖ ^ 2 := by
              rw [hcoeff, one_mul]
    calc
      ‖defect i k‖ ^ 2 = (α i / (1 - α i)) * defectWeight i k := hrewrite.symm
      _ ≤ (α i / (1 - α i)) * (s k - s (k + 1)) := by
            exact mul_le_mul_of_nonneg_left (hweighted_le k) hscale_nonneg
  have hdefect_sq_rhs_tendsto_zero :
      Tendsto (fun k ↦ (α i / (1 - α i)) * (s k - s (k + 1))) atTop (𝓝 (0 : ℝ)) := by
    simpa using hdrop_tendsto_zero.const_mul (α i / (1 - α i))
  have hdefect_sq_tendsto_zero :
      Tendsto (fun k ↦ ‖defect i k‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    refine squeeze_zero' (f := fun k ↦ ‖defect i k‖ ^ 2)
      (g := fun k ↦ (α i / (1 - α i)) * (s k - s (k + 1)))
      (Eventually.of_forall fun k ↦ sq_nonneg ‖defect i k‖)
      (Eventually.of_forall hdefect_sq_le) hdefect_sq_rhs_tendsto_zero
  have hnorm_tendsto_zero :
      Tendsto (fun k ↦ ‖defect i k‖) atTop (𝓝 (0 : ℝ)) := by
    -- Passing through `Real.sqrt` converts the squared-norm convergence into norm convergence.
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (defect i 0))] using
      hdefect_sq_tendsto_zero.sqrt
  -- Strong convergence is equivalent to norm convergence to zero.
  simpa [S, xk, defect] using (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_tendsto_zero

/-- Helper for Theorem 5.23: for a positive index, the Proposition 4.35 defect is exactly the
gap between two consecutive cyclic shadows. -/
private theorem cyclicShadow_positive_defect_eq_gap {n : ℕ}
    (T : Fin (n + 1) → D → D) (i : Fin n) (x : D) :
    (((cyclicShadow T (cyclicNext i.succ) x : D) : H) -
        ((T i.succ (cyclicShadow T (cyclicNext i.succ) x) : D) : H)) =
      (((cyclicShadow T (cyclicNext i.succ) x : D) : H) -
        ((cyclicShadow T i.succ x : D) : H)) := by
  -- Positive shadows are obtained by applying the current operator to the next shadow.
  rw [cyclicShadow_succ_apply]

/-- Helper for Theorem 5.23: every positive adjacent cyclic-shadow gap along the Picard orbit
converges strongly to the corresponding gap at a fixed point. -/
private theorem cyclicShadow_gap_tendsto_of_picard_orbit {n : ℕ}
    (T : Fin (n + 1) → D → D) (α : Fin (n + 1) → ℝ)
    (hαIoo : ∀ i, α i ∈ Set.Ioo (0 : ℝ) 1)
    (hAveraged : ∀ i, AveragedWith (α i) (fun x : D ↦ (T i x : H)))
    (x₀ : D) {z : D} (hz : z ∈ fixedPoints (finiteComposition T))
    (i : Fin n) :
    let S : D → D := finiteComposition T
    let xk : ℕ → D := fun k ↦ (S^[k]) x₀
    Tendsto
      (fun k ↦
        ((cyclicShadow T (cyclicNext i.succ) (xk k) : D) : H) -
          ((cyclicShadow T i.succ (xk k) : D) : H))
      atTop
      (𝓝 ((((cyclicShadow T (cyclicNext i.succ) z : D) : H) -
        ((cyclicShadow T i.succ z : D) : H)))) := by
  let S : D → D := finiteComposition T
  let xk : ℕ → D := fun k ↦ (S^[k]) x₀
  have hdefect :
      Tendsto
        (fun k ↦
          ((((cyclicShadow T (cyclicNext i.succ) (xk k) : D) : H) -
                ((T i.succ (cyclicShadow T (cyclicNext i.succ) (xk k)) : D) : H))) -
              ((((cyclicShadow T (cyclicNext i.succ) z : D) : H) -
                ((T i.succ (cyclicShadow T (cyclicNext i.succ) z) : D) : H))))
        atTop (𝓝 (0 : H)) := by
    simpa [S, xk] using
      cyclicShadow_defect_tendsto_zero_of_picard_orbit T α hαIoo hAveraged x₀ hz i.succ
  have hz_cycle : cyclicShadow T i.succ z = T i.succ (cyclicShadow T (cyclicNext i.succ) z) := by
    simpa using cyclicShadow_cycle_eq_of_mem_fixedPoints (T := T) hz i.succ
  have hgap_sub :
      Tendsto
        (fun k ↦
          ((((cyclicShadow T (cyclicNext i.succ) (xk k) : D) : H) -
                ((cyclicShadow T i.succ (xk k) : D) : H))) -
              ((((cyclicShadow T (cyclicNext i.succ) z : D) : H) -
                ((cyclicShadow T i.succ z : D) : H))))
        atTop (𝓝 (0 : H)) := by
    -- Rewrite the positive defect terms as adjacent shadow gaps.
    simpa [cyclicShadow_positive_defect_eq_gap (T := T) (i := i), hz_cycle] using hdefect
  have hconst :
      Tendsto
        (fun _ : ℕ ↦
          (((cyclicShadow T (cyclicNext i.succ) z : D) : H) -
            ((cyclicShadow T i.succ z : D) : H)))
        atTop
        (𝓝 ((((cyclicShadow T (cyclicNext i.succ) z : D) : H) -
          ((cyclicShadow T i.succ z : D) : H)))) :=
    tendsto_const_nhds
  -- Adding back the limiting gap recovers convergence of the shadow gap itself.
  convert hgap_sub.add hconst using 1
  · funext k
    simp [S, xk, sub_eq_add_neg]
    abel_nf
  · simp

/-- Helper for Theorem 5.23: if `uₖ ⇀ u` and the gaps `uₖ - vₖ` converge strongly to `u - v`,
then `vₖ ⇀ v`. -/
private theorem tendsto_weakly_of_tendsto_weakly_of_sub_tendsto {u v : ℕ → H}
    {uLim vLim : H}
    (hu :
      Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) atTop
        (𝓝 (toWeakSpace ℝ H uLim)))
    (hsub : Tendsto (fun k ↦ u k - v k) atTop (𝓝 (uLim - vLim))) :
    Tendsto (fun k ↦ toWeakSpace ℝ H (v k)) atTop
      (𝓝 (toWeakSpace ℝ H vLim)) := by
  have hsubWeak :
      Tendsto (fun k ↦ toWeakSpace ℝ H (u k - v k)) atTop
        (𝓝 (toWeakSpace ℝ H (uLim - vLim))) := by
    -- Strong convergence transports to the weak space through the canonical continuous map.
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      (((toWeakSpaceCLM ℝ H).continuous.tendsto (uLim - vLim)).comp hsub)
  -- Subtract the convergent gap from the weakly convergent leading sequence.
  simpa [toWeakSpace, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu.sub hsubWeak

-- Proof sketch: the composition of averaged operators is nonexpansive, and the descent estimate
-- from Proposition 4.35 yields asymptotic regularity of the Picard orbit. Apply Theorem 5.14 to
-- the composition to obtain the weak limit of the iterates, then pass successively to the tail
-- compositions using the residual identities to recover the cyclic weak limits
-- and their fixed-point identities.
/-- Theorem 5.23: for a finite family `T 0, ..., T n` of averaged self-maps of a nonempty closed
convex subset of a real Hilbert space, if the ordered composition has a fixed point, then the
Picard residuals converge strongly to `0`, and the Picard orbit admits cyclic weak limits whose
shadow convergences, cyclic relations, and cyclic fixed-point identities encode (5.24)--(5.28). -/
theorem residual_tendsto_zero_and_exists_cyclicWeakLimits_of_averaged_finiteComposition
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {n : ℕ}
    (T : Fin (n + 1) → D → D)
    (hAveraged : ∀ i, ∃ α : ℝ, AveragedWith α (fun x : D ↦ (T i x : H)))
    (hFix : (fixedPoints (finiteComposition T)).Nonempty) (x₀ : D) :
    Tendsto
      (fun k ↦ (((finiteComposition T : D → D)^[k]) x₀ : H) -
        ((((finiteComposition T : D → D)^[k.succ]) x₀) : H))
      atTop (𝓝 (0 : H)) ∧
      ∃ y : Fin (n + 1) → D,
        (∀ i : Fin (n + 1),
          Tendsto
            (fun k ↦ toWeakSpace ℝ H
              ((cyclicShadow T i) (((finiteComposition T)^[k]) x₀) : H))
            atTop (𝓝 (toWeakSpace ℝ H (y i : H)))) ∧
        (∀ i : Fin (n + 1), y i = T i (y (cyclicNext i))) ∧
        ∀ i : Fin (n + 1), y i ∈ fixedPoints (cyclicComposition T i) := by
  classical
  choose α hα using hAveraged
  let S : D → D := finiteComposition T
  let xk : ℕ → D := fun k ↦ (S^[k]) x₀
  have hαIoo : ∀ i, α i ∈ Set.Ioo (0 : ℝ) 1 := fun i ↦ (hα i).mem_Ioo
  rcases hFix with ⟨zFix, hzFix⟩
  have hzFix_val : finiteComposition T zFix = zFix := Function.mem_fixedPoints_iff.mp hzFix
  have hresidual :
      Tendsto
        (fun k ↦ (xk k : H) - (xk (k + 1) : H))
        atTop (𝓝 (0 : H)) := by
    let defectOrbit : Fin (n + 1) → ℕ → H := fun i k ↦
      (((cyclicShadow T (cyclicNext i) (xk k) : D) : H) -
        ((T i (cyclicShadow T (cyclicNext i) (xk k)) : D) : H))
    let defectFix : Fin (n + 1) → H := fun i ↦
      (((cyclicShadow T (cyclicNext i) zFix : D) : H) -
        ((T i (cyclicShadow T (cyclicNext i) zFix) : D) : H))
    have hdefect_sum :
        Tendsto
          (fun k ↦ ∑ i : Fin (n + 1), (defectOrbit i k - defectFix i))
          atTop (𝓝 (0 : H)) := by
      -- Sum the defect limits obtained from the Fejér-drop inequality.
      have hsum :
          Tendsto
            (fun k ↦
              ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), (defectOrbit i k - defectFix i))
            atTop
            (𝓝 (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), (0 : H))) := by
        refine tendsto_finset_sum (Finset.univ : Finset (Fin (n + 1))) ?_
        intro i hi
        simpa [S, xk, defectOrbit, defectFix] using
          cyclicShadow_defect_tendsto_zero_of_picard_orbit T α hαIoo hα x₀ hzFix i
      simpa using hsum
    have hdefectFix_sum : ∑ i : Fin (n + 1), defectFix i = (0 : H) := by
      -- The defect sum at a fixed point is exactly the zero residual.
      calc
        ∑ i : Fin (n + 1), defectFix i
            = ((zFix : D) : H) - ((finiteComposition T zFix : D) : H) := by
                simpa [defectFix] using cyclicShadow_defect_sum_eq_picard_residual T zFix
        _ = 0 := by
              simp [hzFix_val]
    have hresidual_eq :
        (fun k ↦ ∑ i : Fin (n + 1), (defectOrbit i k - defectFix i)) =
          (fun k ↦ (xk k : H) - (xk (k + 1) : H)) := by
      funext k
      -- The defect chain telescopes to the Picard residual, and the fixed-point shadow sum vanishes.
      calc
        ∑ i : Fin (n + 1), (defectOrbit i k - defectFix i)
            = (∑ i : Fin (n + 1), defectOrbit i k) - ∑ i : Fin (n + 1), defectFix i := by
                simp [sub_eq_add_neg, Finset.sum_add_distrib]
        _ =
            (((xk k : D) : H) - ((finiteComposition T (xk k) : D) : H)) -
              (0 : H) := by
              rw [cyclicShadow_defect_sum_eq_picard_residual, hdefectFix_sum]
        _ = ((xk k : D) : H) - ((finiteComposition T (xk k) : D) : H) := by
              simp
        _ = (xk k : H) - (xk (k + 1) : H) := by
              simp [S, xk, Function.iterate_succ_apply']
    rw [hresidual_eq] at hdefect_sum
    exact hdefect_sum
  have hS_nonexpansive : LipschitzWith 1 S := by
    -- Averaged factors are nonexpansive, so their ordered composition is as well.
    simpa [S] using
      lipschitzWith_one_finiteComposition_of_averaged T (fun i ↦ ⟨α i, hα i⟩)
  rcases
      tendsto_weakly_iterates_to_fixedPoint_of_residual_tendsto_zero_of_nonexpansive
        hD_closed hD_convex (T := S) hS_nonexpansive ⟨zFix, hzFix⟩ x₀ (by
          simpa [S, xk, Function.iterate_succ_apply'] using hresidual) with
    ⟨y₁, hy₁Fix, hy₁Weak⟩
  let y : Fin (n + 1) → D := fun i ↦ cyclicShadow T i y₁
  have hy_cycle : ∀ i : Fin (n + 1), y i = T i (y (cyclicNext i)) := by
    intro i
    -- The cyclic relations for the limit cycle are inherited from the fixed-point relation of `y₁`.
    simpa [y] using cyclicShadow_cycle_eq_of_mem_fixedPoints (T := T) hy₁Fix i
  have hy_fixed : ∀ i : Fin (n + 1), y i ∈ fixedPoints (cyclicComposition T i) := by
    intro i
    -- Each shadow point lies in the fixed-point set of the corresponding cyclic rotation.
    simpa [y] using
      cyclicShadow_mem_fixedPoints_cyclicComposition_of_mem_fixedPoints (T := T) hy₁Fix i
  let shadowSeq : Fin (n + 1) → ℕ → H := fun i k ↦ ((cyclicShadow T i (xk k) : D) : H)
  have hshadowNextWeak :
      ∀ i : Fin (n + 1),
        Tendsto (fun k ↦ toWeakSpace ℝ H (shadowSeq (cyclicNext i) k)) atTop
          (𝓝 (toWeakSpace ℝ H (y (cyclicNext i) : H))) := by
    refine Fin.reverseInduction ?_ ?_
    · have hnext_last : cyclicNext (Fin.last n) = (0 : Fin (n + 1)) := by
        apply Fin.ext
        simp [cyclicNext_eq_add_one]
      -- The cyclic successor of the last index is the original Picard orbit.
      simpa [shadowSeq, y, S, xk, hnext_last] using hy₁Weak
    · intro i ih
      have hgap :
          Tendsto
            (fun k ↦ shadowSeq (cyclicNext i.succ) k - shadowSeq i.succ k)
            atTop
            (𝓝 (((y (cyclicNext i.succ) : H) - (y i.succ : H)))) := by
        -- The defect chain supplies the strong limit of the adjacent positive shadow gap.
        simpa [shadowSeq, y, S, xk] using
          cyclicShadow_gap_tendsto_of_picard_orbit T α hαIoo hα x₀ hy₁Fix i
      have hcurr :
          Tendsto (fun k ↦ toWeakSpace ℝ H (shadowSeq i.succ k)) atTop
            (𝓝 (toWeakSpace ℝ H (y i.succ : H))) :=
        tendsto_weakly_of_tendsto_weakly_of_sub_tendsto ih hgap
      have hnext_cast : cyclicNext (i.castSucc : Fin (n + 1)) = i.succ := by
        rw [cyclicNext_eq_add_one]
        apply Fin.ext
        rw [Fin.val_add_one_of_lt]
        · simp [Fin.val_succ]
        · rw [Fin.lt_def, Fin.val_last]
          exact i.isLt
      -- Reindex the predecessor step so the reverse induction advances one shadow backward.
      simpa [shadowSeq, y, hnext_cast] using hcurr
  refine ⟨by simpa [S, xk, Nat.succ_eq_add_one] using hresidual, y, ?_⟩
  refine ⟨?_, hy_cycle, hy_fixed⟩
  intro i
  cases i using Fin.cases with
  | zero =>
      have hnext_last : cyclicNext (Fin.last n) = (0 : Fin (n + 1)) := by
        apply Fin.ext
        simp [cyclicNext_eq_add_one]
      -- The orbit itself is the `0`th cyclic shadow.
      simpa [shadowSeq, y, hnext_last] using hshadowNextWeak (Fin.last n)
  | succ i =>
      have hnext_cast : cyclicNext (i.castSucc : Fin (n + 1)) = i.succ := by
        rw [cyclicNext_eq_add_one]
        apply Fin.ext
        rw [Fin.val_add_one_of_lt]
        · simp [Fin.val_succ]
        · rw [Fin.lt_def, Fin.val_last]
          exact i.isLt
      -- Every positive shadow is obtained as the cyclic successor of its predecessor index.
      simpa [shadowSeq, y, hnext_cast] using hshadowNextWeak i.castSucc

end
