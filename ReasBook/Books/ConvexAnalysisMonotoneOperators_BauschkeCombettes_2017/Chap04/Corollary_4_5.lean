/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_17

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProductSpace

universe u

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: use the polarization identity
-- `‖(2 • T - id) u‖ ^ 2 = ‖u‖ ^ 2 + 4 * ‖T u‖ ^ 2 - 4 * ⟪u, T u⟫_ℝ` to identify clauses
-- (i), (ii), and (iii); transfer (ii) across adjoints using `‖T.adjoint‖ = ‖T‖`; and rewrite
-- clause (iii) as positivity of `T + T.adjoint - 2 • T.adjoint.comp T`.
/- Firm nonexpansiveness of a bounded linear operator is equivalent to the quadratic inequality
obtained by specializing at `y = 0`. -/
private lemma firmly_nonexpansive_iff_quadratic_at_zero (T : H →L[ℝ] H) :
    FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
      ∀ x : H, ‖T x‖ ^ (2 : ℕ) ≤ ⟪x, T x⟫_ℝ := by
  rw [firmlyNonexpansiveOn_univ_iff_norm_sq_le_inner]
  constructor
  · intro hT x
    -- Specializing the defining inequality at `y = 0` produces the quadratic bound.
    simpa [real_inner_comm] using hT x 0
  · intro hT x y
    -- Applying the quadratic bound to `x - y` recovers the difference inequality.
    simpa [map_sub, real_inner_comm] using hT (x - y)

/- The reflector norm bound `‖2T - Id‖ ≤ 1` is equivalent to the quadratic inequality from
clause (iii). -/
private lemma reflector_norm_le_iff_quadratic (T : H →L[ℝ] H) :
    ‖(2 : ℝ) • T - 1‖ ≤ 1 ↔ ∀ x : H, ‖T x‖ ^ (2 : ℕ) ≤ ⟪x, T x⟫_ℝ := by
  constructor
  · intro hnorm x
    -- Convert the operator norm bound to the pointwise reflector contraction.
    have hpointwise :
        ‖((2 : ℝ) • T - 1) x‖ ≤ ‖x‖ := by
      simpa using (ContinuousLinearMap.opNorm_le_iff (show 0 ≤ (1 : ℝ) by positivity)).mp hnorm x
    have hsq :
        ‖((2 : ℝ) • T - 1) x‖ ^ (2 : ℕ) ≤ ‖x‖ ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hpointwise
    have hreflect :
        ‖x‖ ^ (2 : ℕ) - ‖((2 : ℝ) • T - 1) x‖ ^ (2 : ℕ) =
          4 * (⟪x, T x⟫_ℝ - ‖T x‖ ^ (2 : ℕ)) := by
      -- Rewrite the reflector norm with Lemma 2.17 in the form used in the textbook proof.
      simpa using norm_sq_sub_norm_sq_reflection_eq_four_mul x (T x)
    nlinarith
  · intro hquad
    -- Conversely, turn the quadratic inequality back into a pointwise reflector contraction.
    rw [ContinuousLinearMap.opNorm_le_iff (show 0 ≤ (1 : ℝ) by positivity)]
    intro x
    have hreflect :
        ‖x‖ ^ (2 : ℕ) - ‖((2 : ℝ) • T - 1) x‖ ^ (2 : ℕ) =
          4 * (⟪x, T x⟫_ℝ - ‖T x‖ ^ (2 : ℕ)) := by
      simpa using norm_sq_sub_norm_sq_reflection_eq_four_mul x (T x)
    have hsq :
        ‖((2 : ℝ) • T - 1) x‖ ^ (2 : ℕ) ≤ ‖x‖ ^ (2 : ℕ) := by
      nlinarith [hquad x, hreflect]
    simpa using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

variable [CompleteSpace H]

/- The reflector norm bound is invariant under taking adjoints. -/
private lemma adjoint_reflector_norm_le_iff (T : H →L[ℝ] H) :
    ‖(2 : ℝ) • T - 1‖ ≤ 1 ↔ ‖(2 : ℝ) • T.adjoint - 1‖ ≤ 1 := by
  have hid : (1 : H →L[ℝ] H).adjoint = 1 := by
    ext x
    refine ext_inner_right ℝ (fun y ↦ ?_)
    simp [ContinuousLinearMap.adjoint_inner_left]
  have hadj : ((2 : ℝ) • T - 1).adjoint = (2 : ℝ) • T.adjoint - 1 := by
    ext x
    refine ext_inner_right ℝ (fun y ↦ ?_)
    -- The adjoint commutes with the affine reflector construction.
    simp [hid]
  have hnorm :
      ‖(2 : ℝ) • T.adjoint - 1‖ = ‖(2 : ℝ) • T - 1‖ := by
    calc
      ‖(2 : ℝ) • T.adjoint - 1‖ = ‖((2 : ℝ) • T - 1).adjoint‖ := by rw [hadj]
      _ = ‖(2 : ℝ) • T - 1‖ := ContinuousLinearMap.adjoint.norm_map _
  rw [hnorm]

/- Positivity of `T + T† - 2 T†T` is equivalent to the same quadratic inequality as clause (iii). -/
private lemma positive_operator_iff_quadratic (T : H →L[ℝ] H) :
    (T + T.adjoint - (2 : ℝ) • (T.adjoint.comp T)).IsPositive ↔
      ∀ x : H, ‖T x‖ ^ (2 : ℕ) ≤ ⟪x, T x⟫_ℝ := by
  let A : H →L[ℝ] H := T + T.adjoint - (2 : ℝ) • (T.adjoint.comp T)
  have hcomp_symm :
      ∀ x y : H, ⟪(T.adjoint.comp T) x, y⟫_ℝ = ⟪x, (T.adjoint.comp T) y⟫_ℝ := by
    intro x y
    calc
      ⟪(T.adjoint.comp T) x, y⟫_ℝ = ⟪T x, T y⟫_ℝ := by
        simpa [ContinuousLinearMap.comp_apply] using
          (ContinuousLinearMap.adjoint_inner_left T y (T x))
      _ = ⟪x, (T.adjoint.comp T) y⟫_ℝ := by
        simpa [ContinuousLinearMap.comp_apply] using
          (ContinuousLinearMap.adjoint_inner_right T x (T y)).symm
  have hA_symm : A.IsSymmetric := by
    intro x y
    -- Expanding both sides shows that the adjoint terms pair up symmetrically.
    calc
      ⟪A x, y⟫_ℝ
          = ⟪T x, y⟫_ℝ + ⟪T.adjoint x, y⟫_ℝ - 2 * ⟪(T.adjoint.comp T) x, y⟫_ℝ := by
              simp [A, inner_add_left, inner_sub_left, real_inner_smul_left]
      _ = ⟪x, T.adjoint y⟫_ℝ + ⟪x, T y⟫_ℝ - 2 * ⟪x, (T.adjoint.comp T) y⟫_ℝ := by
            rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left,
              hcomp_symm x y]
      _ = ⟪x, A y⟫_ℝ := by
            simp [A, inner_add_right, inner_sub_right, real_inner_smul_right]
            ring
  have hA_apply :
      ∀ x : H, ⟪A x, x⟫_ℝ = 2 * (⟪x, T x⟫_ℝ - ‖T x‖ ^ (2 : ℕ)) := by
    intro x
    have hcomp :
        ⟪(T.adjoint.comp T) x, x⟫_ℝ = ‖T x‖ ^ (2 : ℕ) := by
      calc
        ⟪(T.adjoint.comp T) x, x⟫_ℝ = ⟪T x, T x⟫_ℝ := by
          simpa [ContinuousLinearMap.comp_apply] using
            (ContinuousLinearMap.adjoint_inner_left T x (T x))
        _ = ‖T x‖ ^ (2 : ℕ) := real_inner_self_eq_norm_sq _
    -- This is the quadratic-form computation behind clause (v).
    calc
      ⟪A x, x⟫_ℝ
          = ⟪T x, x⟫_ℝ + ⟪T.adjoint x, x⟫_ℝ - 2 * ⟪(T.adjoint.comp T) x, x⟫_ℝ := by
              simp [A, inner_add_left, inner_sub_left, real_inner_smul_left]
      _ = ⟪x, T x⟫_ℝ + ⟪x, T x⟫_ℝ - 2 * ‖T x‖ ^ (2 : ℕ) := by
            rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left, hcomp]
      _ = 2 * (⟪x, T x⟫_ℝ - ‖T x‖ ^ (2 : ℕ)) := by ring
  constructor
  · intro hpos x
    rcases (ContinuousLinearMap.isPositive_iff A).mp hpos with ⟨_, hnonneg⟩
    -- Positivity of `A` is exactly nonnegativity of the same quadratic form.
    have hnonnegx : 0 ≤ ⟪A x, x⟫_ℝ := hnonneg x
    rw [hA_apply x] at hnonnegx
    nlinarith
  · intro hquad
    -- The quadratic inequality supplies the nonnegativity half of positivity.
    refine (ContinuousLinearMap.isPositive_iff A).mpr ?_
    refine ⟨hA_symm, ?_⟩
    intro x
    rw [hA_apply x]
    nlinarith [hquad x]

/-- For a bounded linear operator on a real Hilbert space, firm nonexpansiveness, the norm
bound `‖2T - Id‖ ≤ 1`, the pointwise inequality `‖T x‖² ≤ ⟪x, T x⟫`, firm nonexpansiveness of
the adjoint, and positivity of `T + T† - 2 T†T` are equivalent. -/
theorem tfae_firmly_nonexpansive_adjoint_norm_quadratic (T : H →L[ℝ] H) :
    List.TFAE
      [ FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x),
        ‖(2 : ℝ) • T - 1‖ ≤ 1,
        ∀ x : H, ‖T x‖ ^ (2 : ℕ) ≤ ⟪x, T x⟫_ℝ,
        FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T.adjoint x),
        (T + T.adjoint - (2 : ℝ) • (T.adjoint.comp T)).IsPositive ] := by
  -- Follow the textbook implication graph by using the quadratic inequality as the common bridge.
  tfae_have 1 ↔ 3 := firmly_nonexpansive_iff_quadratic_at_zero T
  tfae_have 2 ↔ 3 := reflector_norm_le_iff_quadratic T
  tfae_have 2 ↔ 4 := by
    -- Transfer the reflector characterization across adjoints, then reuse the previous bridges.
    calc
      ‖(2 : ℝ) • T - 1‖ ≤ 1 ↔ ‖(2 : ℝ) • T.adjoint - 1‖ ≤ 1 :=
        adjoint_reflector_norm_le_iff T
      _ ↔ FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T.adjoint x) :=
        (reflector_norm_le_iff_quadratic T.adjoint).trans
          (firmly_nonexpansive_iff_quadratic_at_zero T.adjoint).symm
  tfae_have 3 ↔ 5 := (positive_operator_iff_quadratic T).symm
  tfae_finish
