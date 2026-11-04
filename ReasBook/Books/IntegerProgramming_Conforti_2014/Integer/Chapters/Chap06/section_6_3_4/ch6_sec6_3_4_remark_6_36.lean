/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3.ch6_sec6_3_definition_6_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_lemma_6_29

noncomputable section

section Remark636

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "Zq" => Fin q → ℤ
local notation "NatAssignment" => Rq →₀ ℕ
local notation "ContAssignment" => Rq →₀ NNReal

open scoped IntegerVectorNotation

-- Semantic recall note: `lean_leansearch` did not surface a relevant mathlib owner for trivial
-- liftings, so this file keeps the local Section 6.3.4 source-facing API.

/-- A lifting `π` of `ψ` is minimal when any valid Gomory--Johnson pair `(π', ψ)` lying
pointwise below `π` coincides with `π`. -/
class IsMinimalLiftingOf
    (f : Rq)
    (π ψ : Rq → ℝ) : Prop extends IsValidGomoryJohnsonPair f π ψ where
  eq_of_le :
    ∀ {π' : Rq → ℝ},
      IsValidGomoryJohnsonPair f π' ψ →
      π' ≤ π →
      π' = π

namespace IsValidGomoryJohnsonPair

/-- A lifting restricts to the validity inequality for the continuous relaxation `R_f` by taking
zero integer part. -/
theorem continuous_valid
    {f : Rq}
    {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ)
    {y : ContAssignment}
    (hy : f + y.sum (fun r a ↦ (a : ℝ) • r) ∈ ℤ^q) :
    1 ≤ y.sum (fun r a ↦ ψ r * (a : ℝ)) :=
  (toContinuousValidFunction hπψ).one_le ⟨hy⟩

end IsValidGomoryJohnsonPair

/-- For Remark 6.36, the trivial lifting is given by the raw formula
`π̄(r) = inf_{w ∈ ℤ^q} ψ (r + w)`; the validity hypotheses enter through the theorems below, not
through this definition. -/
def trivial_lifting
    (ψ : Rq → ℝ) : Rq → ℝ :=
  fun r ↦
    sInf <| Set.range fun w : Zq ↦ ψ (fun i ↦ r i + (w i : ℝ))

/-- `trivial_lifting ψ r` is the infimum of the integer translates of `ψ` through `r`. -/
@[simp] theorem trivial_lifting_apply
    (ψ : Rq → ℝ)
    (r : Rq) :
    trivial_lifting ψ r =
      sInf (Set.range fun w : Zq ↦ ψ (fun i ↦ r i + (w i : ℝ))) :=
  rfl

/-- Every positive error tolerance is realized by an integer translate whose `ψ`-value lies within
that tolerance above `trivial_lifting ψ r`. -/
lemma exists_translate_lt_trivialLifting_add
    (ψ : Rq → ℝ)
    (r : Rq)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ w : Zq, ψ (fun i ↦ r i + (w i : ℝ)) < trivial_lifting ψ r + ε := by
  let translates : Set ℝ := Set.range fun w : Zq ↦ ψ (fun i ↦ r i + (w i : ℝ))
  have htranslates : translates.Nonempty := by
    exact ⟨_, ⟨0, rfl⟩⟩
  rw [trivial_lifting_apply]
  -- Pick an element of the translate set that is `ε`-close to the infimum.
  rcases Real.lt_sInf_add_pos htranslates hε with ⟨a, ha, hw⟩
  rcases ha with ⟨w, rfl⟩
  exact ⟨w, by simpa [translates] using hw⟩

/-- Erasing the integer mass at `r` and moving it to the continuous side at the translate `r + w`
preserves mixed-integer feasibility. -/
lemma eraseIntegerMassAddTranslate_mem_mixed_integer_relaxation_set
    {f : Rq}
    {x : NatAssignment}
    {y : ContAssignment}
    (r : Rq)
    (w : Zq)
    (hxy : (x, y) ∈ mixed_integer_relaxation_set f) :
    (x.erase r, y + Finsupp.single (fun i ↦ r i + (w i : ℝ)) (x r : NNReal)) ∈
      mixed_integer_relaxation_set f := by
  rw [mem_mixed_integer_relaxation_set_iff] at hxy ⊢
  rcases hxy with ⟨z, hz⟩
  refine ⟨fun i ↦ z i + (x r : ℤ) * w i, ?_⟩
  have hxdecomp : x = x.erase r + Finsupp.single r (x r) := by
    simpa using
      (Finsupp.update_eq_erase_add_single x r (x r))
  have hxsum :
      x.sum (fun s n ↦ (n : ℝ) • s) =
        (x.erase r).sum (fun s n ↦ (n : ℝ) • s) + (x r : ℝ) • r := by
    -- Split the integer assignment into the erased part and the single column at `r`.
    rw [hxdecomp, Finsupp.sum_add_index]
    · simp
    · intro s
      simp
    · intro s a b
      simp [Nat.cast_add, add_smul]
  have hysum :
      (y + Finsupp.single (fun i ↦ r i + (w i : ℝ)) (x r : NNReal)).sum
          (fun s a ↦ (a : ℝ) • s) =
        y.sum (fun s a ↦ (a : ℝ) • s) +
          (x r : ℝ) • (fun i ↦ r i + (w i : ℝ)) := by
    -- The added continuous singleton contributes exactly `(x r) • (r + w)`.
    rw [Finsupp.sum_add_index]
    · simp
    · intro s
      simp
    · intro s a b
      simp [NNReal.coe_add, add_smul]
  calc
    f + (x.erase r).sum (fun s n ↦ (n : ℝ) • s) +
        (y + Finsupp.single (fun i ↦ r i + (w i : ℝ)) (x r : NNReal)).sum
          (fun s a ↦ (a : ℝ) • s)
        =
          f + x.sum (fun s n ↦ (n : ℝ) • s) + y.sum (fun s a ↦ (a : ℝ) • s) +
            (x r : ℝ) • (fun i ↦ (w i : ℝ)) := by
              -- After the erase/single decompositions, the net balance shifts by `(x r) • w`.
              rw [hxsum, hysum]
              ext i
              simp [Pi.add_apply, Pi.smul_apply]
              ring
    _ = fun i ↦ ((z i : ℤ) : ℝ) + (x r : ℝ) * (w i : ℝ) := by
          -- Rewrite the original feasible balance through its lattice witness `z`.
          rw [hz]
          ext i
          simp [Pi.add_apply, Pi.smul_apply]
    _ = fun i ↦ ((z i + (x r : ℤ) * w i : ℤ) : ℝ) := by
          -- Coordinatewise, the extra shift is the integer vector `(x r) • w`.
          ext i
          rw [Int.cast_add, Int.cast_mul, Int.cast_natCast]

/-- If the translate value `ψ (r + w)` is nonnegative, then lowering the integer coefficient at
`r` to that translate value preserves mixed validity. -/
lemma replaceAtWithIntegerTranslateValid
    {f : Rq}
    {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ)
    (r : Rq)
    (w : Zq)
    (htrans_nonneg : 0 ≤ ψ (fun i ↦ r i + (w i : ℝ))) :
    IsValidGomoryJohnsonPair f
      (fun s ↦ if s = r then ψ (fun i ↦ r i + (w i : ℝ)) else π s) ψ := by
  refine
    { nonneg := ?_
      one_le := ?_ }
  · intro s
    by_cases hs : s = r
    · -- At the lowered point we use the assumed nonnegativity of the translate value.
      simp [hs, htrans_nonneg]
    · -- Away from `r`, the coefficients are unchanged.
      simp [hs, hπψ.nonneg s]
  · intro x y hxy
    let y' : ContAssignment :=
      y + Finsupp.single (fun i ↦ r i + (w i : ℝ)) (x r : NNReal)
    have hy' :
        (x.erase r, y') ∈ mixed_integer_relaxation_set f :=
      eraseIntegerMassAddTranslate_mem_mixed_integer_relaxation_set r w hxy
    have hbase :
        1 ≤
          (x.erase r).sum (fun s n ↦ π s * (n : ℝ)) +
            y'.sum (fun s a ↦ ψ s * (a : ℝ)) :=
      hπψ.one_le hy'
    have hxdecomp : x = x.erase r + Finsupp.single r (x r) := by
      simpa using
        (Finsupp.update_eq_erase_add_single x r (x r))
    have herase :
        (x.erase r).sum
            (fun s n ↦
              (if s = r then ψ (fun i ↦ r i + (w i : ℝ)) else π s) * (n : ℝ)) =
          (x.erase r).sum (fun s n ↦ π s * (n : ℝ)) := by
      refine Finsupp.sum_congr ?_
      intro s hs
      have hsne : s ≠ r := by
        intro hsr
        have hs0 : (x.erase r) s ≠ 0 :=
          Finsupp.mem_support_iff.mp hs
        simp [hsr] at hs0
      simp [hsne]
    have hρsum :
        x.sum
            (fun s n ↦
              (if s = r then ψ (fun i ↦ r i + (w i : ℝ)) else π s) * (n : ℝ)) =
          (x.erase r).sum (fun s n ↦ π s * (n : ℝ)) +
            ψ (fun i ↦ r i + (w i : ℝ)) * (x r : ℝ) := by
      -- Only the coefficient at `r` changes, so the new integer sum is the old erased sum plus
      -- one translate term.
      rw [hxdecomp, Finsupp.sum_add_index]
      · rw [herase]
        simp
      · intro s
        simp
      · intro s a b
        simp [Nat.cast_add, left_distrib]
    have hy'sum :
        y'.sum (fun s a ↦ ψ s * (a : ℝ)) =
          y.sum (fun s a ↦ ψ s * (a : ℝ)) +
            ψ (fun i ↦ r i + (w i : ℝ)) * (x r : ℝ) := by
      -- The added continuous singleton contributes the same translate term to the `ψ`-sum.
      dsimp [y']
      rw [Finsupp.sum_add_index]
      · simp
      · intro s
        simp
      · intro s a b
        simp [NNReal.coe_add, left_distrib]
    calc
      1 ≤
          (x.erase r).sum (fun s n ↦ π s * (n : ℝ)) +
            y'.sum (fun s a ↦ ψ s * (a : ℝ)) := hbase
      _ =
          x.sum
              (fun s n ↦
                (if s = r then ψ (fun i ↦ r i + (w i : ℝ)) else π s) * (n : ℝ)) +
            y.sum (fun s a ↦ ψ s * (a : ℝ)) := by
              rw [hρsum, hy'sum]
              ring

/-- Replacing the coefficient at one column by any nonnegative upper bound of
`trivial_lifting ψ r` preserves mixed validity. -/
lemma replaceAtWithTrivialLiftingBoundValid
    {f : Rq}
    {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ)
    (r : Rq)
    (a : ℝ)
    (ha_nonneg : 0 ≤ a)
    (htrivial : trivial_lifting ψ r ≤ a) :
    IsValidGomoryJohnsonPair f
      (fun s ↦ if s = r then a else π s) ψ := by
  refine
    { nonneg := ?_
      one_le := ?_ }
  · intro s
    by_cases hs : s = r
    · -- At the replaced point we use the assumed nonnegativity of `a`.
      simp [hs, ha_nonneg]
    · -- Away from `r`, the original nonnegativity is unchanged.
      simp [hs, hπψ.nonneg s]
  · intro x y hxy
    -- Route correction: use a near-minimizing translate of `trivial_lifting ψ r` and absorb the
    -- resulting error by `le_of_forall_pos_le_add`, instead of forcing a raw translate to be
    -- pointwise nonnegative first.
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    let δ : ℝ := ε / ((x r : ℝ) + 1)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    rcases exists_translate_lt_trivialLifting_add ψ r hδ_pos with ⟨w, hw⟩
    let y' : ContAssignment :=
      y + Finsupp.single (fun i ↦ r i + (w i : ℝ)) (x r : NNReal)
    have hy' :
        (x.erase r, y') ∈ mixed_integer_relaxation_set f :=
      eraseIntegerMassAddTranslate_mem_mixed_integer_relaxation_set r w hxy
    have hbase :
        1 ≤
          (x.erase r).sum (fun s n ↦ π s * (n : ℝ)) +
            y'.sum (fun s a ↦ ψ s * (a : ℝ)) :=
      hπψ.one_le hy'
    have hxdecomp : x = x.erase r + Finsupp.single r (x r) := by
      simpa using
        (Finsupp.update_eq_erase_add_single x r (x r))
    have herase :
        (x.erase r).sum
            (fun s n ↦
              (if s = r then a else π s) * (n : ℝ)) =
          (x.erase r).sum (fun s n ↦ π s * (n : ℝ)) := by
      refine Finsupp.sum_congr ?_
      intro s hs
      have hsne : s ≠ r := by
        intro hsr
        have hs0 : (x.erase r) s ≠ 0 :=
          Finsupp.mem_support_iff.mp hs
        simp [hsr] at hs0
      simp [hsne]
    have hρsum :
        x.sum
            (fun s n ↦
              (if s = r then a else π s) * (n : ℝ)) =
          (x.erase r).sum (fun s n ↦ π s * (n : ℝ)) +
            a * (x r : ℝ) := by
      -- Only the coefficient at `r` is modified, so the integer part splits into the erased sum
      -- and the new coefficient at `r`.
      rw [hxdecomp, Finsupp.sum_add_index]
      · rw [herase]
        simp
      · intro s
        simp
      · intro s a b
        simp [Nat.cast_add, left_distrib]
    have hy'sum :
        y'.sum (fun s a ↦ ψ s * (a : ℝ)) =
          y.sum (fun s a ↦ ψ s * (a : ℝ)) +
            ψ (fun i ↦ r i + (w i : ℝ)) * (x r : ℝ) := by
      -- The transported continuous singleton contributes exactly the translate term.
      dsimp [y']
      rw [Finsupp.sum_add_index]
      · simp
      · intro s
        simp
      · intro s a b
        simp [NNReal.coe_add, left_distrib]
    have hx_nonneg : 0 ≤ (x r : ℝ) := by
      exact_mod_cast Nat.zero_le (x r)
    have hwle : ψ (fun i ↦ r i + (w i : ℝ)) ≤ a + δ := by
      -- The near-minimizer sits above the infimum but within the chosen tolerance.
      exact le_of_lt <|
        lt_of_lt_of_le hw <|
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right htrivial δ
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
    have hδmul : δ * (x r : ℝ) ≤ ε := by
      have hx_le : (x r : ℝ) ≤ (x r : ℝ) + 1 := by
        linarith
      calc
        δ * (x r : ℝ) ≤ δ * ((x r : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_left hx_le hδ_nonneg
        _ = ε := by
          dsimp [δ]
          have hden_pos : 0 < ((x r : ℝ) + 1) := by positivity
          have hden : ((x r : ℝ) + 1) ≠ 0 := ne_of_gt hden_pos
          field_simp [hden]
    have happrox :
        ψ (fun i ↦ r i + (w i : ℝ)) * (x r : ℝ) ≤
          a * (x r : ℝ) + ε := by
      calc
        ψ (fun i ↦ r i + (w i : ℝ)) * (x r : ℝ) ≤
            (a + δ) * (x r : ℝ) := by
              exact mul_le_mul_of_nonneg_right hwle hx_nonneg
        _ = a * (x r : ℝ) + δ * (x r : ℝ) := by ring
        _ ≤ a * (x r : ℝ) + ε := by
              linarith
    have hbase' :
        1 ≤
          (x.erase r).sum (fun s n ↦ π s * (n : ℝ)) +
            y.sum (fun s a ↦ ψ s * (a : ℝ)) +
              ψ (fun i ↦ r i + (w i : ℝ)) * (x r : ℝ) := by
      -- Rewrite the transported continuous sum back into the original `y`-sum plus one translate.
      rw [hy'sum] at hbase
      simpa [add_assoc, add_left_comm, add_comm] using hbase
    calc
      1 ≤
          (x.erase r).sum (fun s n ↦ π s * (n : ℝ)) +
            y.sum (fun s a ↦ ψ s * (a : ℝ)) +
              ψ (fun i ↦ r i + (w i : ℝ)) * (x r : ℝ) := hbase'
      _ ≤
          (x.erase r).sum (fun s n ↦ π s * (n : ℝ)) +
            y.sum (fun s a ↦ ψ s * (a : ℝ)) +
              (a * (x r : ℝ) + ε) := by
                linarith
      _ =
          x.sum
              (fun s n ↦
                (if s = r then a else π s) * (n : ℝ)) +
            y.sum (fun s a ↦ ψ s * (a : ℝ)) + ε := by
              rw [hρsum]
              ring

/-- When `trivial_lifting ψ r` already lies below `π r` and is nonnegative, one can choose a
nonnegative intermediate coefficient strictly between them. -/
lemma existsUpperBoundBetweenTrivialAndPi
    {ψ π : Rq → ℝ}
    (r : Rq)
    (htrivial_nonneg : 0 ≤ trivial_lifting ψ r)
    (htrivial_lt : trivial_lifting ψ r < π r) :
    ∃ a : ℝ, 0 ≤ a ∧ trivial_lifting ψ r ≤ a ∧ a < π r := by
  refine ⟨(trivial_lifting ψ r + π r) / 2, ?_⟩
  constructor
  · -- The midpoint is nonnegative because the lower endpoint already is.
    linarith
  constructor
  · -- The midpoint lies above `trivial_lifting ψ r`.
    linarith
  · -- The midpoint still lies strictly below `π r`.
    linarith

/-- Helper for Remark 6.36: choose one integer translate for each column of `x` so that the total
translated `ψ`-sum stays within `ε` of the weighted trivial-lifting sum. -/
lemma existsTranslateChoiceWeightedApprox
    (ψ : Rq → ℝ)
    (x : NatAssignment)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ σ : Rq → Zq,
      x.sum (fun r n ↦ ψ (fun i ↦ r i + (σ r i : ℝ)) * (n : ℝ)) ≤
        x.sum (fun r n ↦ trivial_lifting ψ r * (n : ℝ)) + ε := by
  classical
  let totalMass : ℝ := x.sum (fun _ n ↦ (n : ℝ))
  let δ : ℝ := ε / (totalMass + 1)
  have hmass_nonneg : 0 ≤ totalMass := by
    dsimp [totalMass]
    refine Finsupp.sum_nonneg ?_
    intro r hr
    exact_mod_cast Nat.zero_le (x r)
  have hδ_pos : 0 < δ := by
    have hden_pos : 0 < totalMass + 1 := by
      linarith
    dsimp [δ]
    exact div_pos hε hden_pos
  have hchoose :
      ∀ r : Rq, ∃ w : Zq, ψ (fun i ↦ r i + (w i : ℝ)) < trivial_lifting ψ r + δ := by
    intro r
    exact exists_translate_lt_trivialLifting_add ψ r hδ_pos
  choose σ hσ using hchoose
  refine ⟨σ, ?_⟩
  have hpoint :
      ∀ r : Rq,
        ψ (fun i ↦ r i + (σ r i : ℝ)) * (x r : ℝ) ≤
          trivial_lifting ψ r * (x r : ℝ) + δ * (x r : ℝ) := by
    intro r
    have hx_nonneg : 0 ≤ (x r : ℝ) := by
      exact_mod_cast Nat.zero_le (x r)
    have hσle :
        ψ (fun i ↦ r i + (σ r i : ℝ)) ≤ trivial_lifting ψ r + δ :=
      le_of_lt (hσ r)
    calc
      ψ (fun i ↦ r i + (σ r i : ℝ)) * (x r : ℝ) ≤
          (trivial_lifting ψ r + δ) * (x r : ℝ) := by
            exact mul_le_mul_of_nonneg_right hσle hx_nonneg
      _ = trivial_lifting ψ r * (x r : ℝ) + δ * (x r : ℝ) := by
            ring
  have hsplit :
      x.sum (fun r n ↦ trivial_lifting ψ r * (n : ℝ) + δ * (n : ℝ)) =
        x.sum (fun r n ↦ trivial_lifting ψ r * (n : ℝ)) +
          δ * x.sum (fun _ n ↦ (n : ℝ)) := by
    -- Expand the weighted sum once so the approximation error is grouped into `δ * totalMass`.
    rw [Finsupp.sum, Finsupp.sum, Finsupp.sum, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
  have hδmul :
      δ * x.sum (fun _ n ↦ (n : ℝ)) ≤ ε := by
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
    have hmass_le :
        x.sum (fun _ n ↦ (n : ℝ)) ≤ x.sum (fun _ n ↦ (n : ℝ)) + 1 := by
      linarith
    calc
      δ * x.sum (fun _ n ↦ (n : ℝ)) ≤
          δ * (x.sum (fun _ n ↦ (n : ℝ)) + 1) := by
            exact mul_le_mul_of_nonneg_left hmass_le hδ_nonneg
      _ = ε := by
            dsimp [δ, totalMass]
            have hden_pos :
                0 < x.sum (fun _ n ↦ (n : ℝ)) + 1 := by
              have : 0 ≤ x.sum (fun _ n ↦ (n : ℝ)) := by
                refine Finsupp.sum_nonneg ?_
                intro r hr
                exact_mod_cast Nat.zero_le (x r)
              linarith
            have hden_ne :
                x.sum (fun _ n ↦ (n : ℝ)) + 1 ≠ 0 :=
              ne_of_gt hden_pos
            field_simp [hden_ne]
  -- Sum the pointwise approximation bounds over the finite support of `x`.
  rw [Finsupp.sum, Finsupp.sum]
  calc
    Finset.sum x.support (fun r ↦ ψ (fun i ↦ r i + (σ r i : ℝ)) * (x r : ℝ)) ≤
        Finset.sum x.support
          (fun r ↦ trivial_lifting ψ r * (x r : ℝ) + δ * (x r : ℝ)) := by
            exact Finset.sum_le_sum fun r _ ↦ hpoint r
    _ = x.sum (fun r n ↦ trivial_lifting ψ r * (n : ℝ)) +
          δ * x.sum (fun _ n ↦ (n : ℝ)) := hsplit
    _ ≤ x.sum (fun r n ↦ trivial_lifting ψ r * (n : ℝ)) + ε := by
          linarith

/-- Helper for Remark 6.36: transporting every integer column of a mixed-feasible point to the
continuous side along chosen integer translates produces a continuous-feasible point. -/
lemma transportIntegerMassToContinuousFeasible
    {f : Rq}
    {x : NatAssignment}
    {y : ContAssignment}
    (σ : Rq → Zq)
    (hxy : (x, y) ∈ mixed_integer_relaxation_set f) :
    let yσ : ContAssignment :=
      y + x.sum (fun r n ↦ Finsupp.single (fun i ↦ r i + (σ r i : ℝ)) (n : NNReal))
    yσ ∈ continuous_infinite_relaxation_feasible_set f := by
  classical
  let transported :
      NatAssignment → ContAssignment → Prop :=
    fun x y ↦
      ((0 : NatAssignment),
        y + x.sum (fun r n ↦ Finsupp.single (fun i ↦ r i + (σ r i : ℝ)) (n : NNReal))) ∈
          mixed_integer_relaxation_set f
  have htransport :
      ∀ {x : NatAssignment} {y : ContAssignment},
        (x, y) ∈ mixed_integer_relaxation_set f → transported x y := by
    intro x y hxy
    induction x using Finsupp.induction generalizing y with
    | zero =>
      -- With no integer mass left, the transported continuous assignment is the original one.
      simpa [transported]
        using hxy
    | single_add r n x hr hn ih =>
      have hx_r : x r = 0 := by
        simpa [Finsupp.mem_support_iff] using hr
      have herase :
          (Finsupp.single r n + x).erase r = x := by
        ext s
        by_cases hs : s = r
        · subst hs
          simp [hx_r]
        · simp [hs]
      have hstep :
          (x, y + Finsupp.single (fun i ↦ r i + (σ r i : ℝ)) (n : NNReal)) ∈
            mixed_integer_relaxation_set f := by
        simpa [herase, hx_r]
          using
            (eraseIntegerMassAddTranslate_mem_mixed_integer_relaxation_set
              (x := Finsupp.single r n + x) (y := y) r (σ r) hxy)
      have htail :=
        ih
          (y := y + Finsupp.single (fun i ↦ r i + (σ r i : ℝ)) (n : NNReal))
          hstep
      have hsum :
          (Finsupp.single r n + x).sum
              (fun s m ↦ Finsupp.single (fun i ↦ s i + (σ s i : ℝ)) (m : NNReal)) =
            Finsupp.single (fun i ↦ r i + (σ r i : ℝ)) (n : NNReal) +
              x.sum (fun s m ↦ Finsupp.single (fun i ↦ s i + (σ s i : ℝ)) (m : NNReal)) := by
        -- Split the transport sum into the new singleton translate and the induction tail.
        rw [Finsupp.sum_add_index]
        · simp
        · simp
        · intro s a b₁ b₂
          ext t
          simp [NNReal.coe_add]
      -- Reassociate the transported continuous sum so it matches the induction hypothesis.
      simpa [transported, hsum, add_assoc]
        using htail
  have hzero :
      ((0 : NatAssignment),
        y + x.sum (fun r n ↦ Finsupp.single (fun i ↦ r i + (σ r i : ℝ)) (n : NNReal))) ∈
          mixed_integer_relaxation_set f :=
    htransport hxy
  rw [mem_continuous_infinite_relaxation_feasible_set_iff]
  rw [mem_mixed_integer_relaxation_set_iff] at hzero
  rcases hzero with ⟨z, hz⟩
  refine (mem_integerVectors_iff).2 ?_
  refine ⟨z, ?_⟩
  simpa using hz

/-- Helper for Remark 6.36: transporting integer mass to the continuous side rewrites the
continuous `ψ`-sum as the original `y`-sum plus the translated integer contribution. -/
lemma transportedContinuousAssignmentCutSum
    (ψ : Rq → ℝ)
    (σ : Rq → Zq)
    (x : NatAssignment)
    (y : ContAssignment) :
    (y + x.sum (fun r n ↦ Finsupp.single (fun i ↦ r i + (σ r i : ℝ)) (n : NNReal))).sum
        (fun s a ↦ ψ s * (a : ℝ)) =
      y.sum (fun s a ↦ ψ s * (a : ℝ)) +
        x.sum (fun r n ↦ ψ (fun i ↦ r i + (σ r i : ℝ)) * (n : ℝ)) := by
  classical
  induction x using Finsupp.induction generalizing y with
  | zero =>
      -- With no transported integer mass, the rewritten cut sum is unchanged.
      simp
  | single_add r n x hr hn ih =>
      have hx_r : x r = 0 := by
        simpa [Finsupp.mem_support_iff] using hr
      have hsum :
          (Finsupp.single r n + x).sum
              (fun s m ↦ Finsupp.single (fun i ↦ s i + (σ s i : ℝ)) (m : NNReal)) =
            Finsupp.single (fun i ↦ r i + (σ r i : ℝ)) (n : NNReal) +
              x.sum (fun s m ↦ Finsupp.single (fun i ↦ s i + (σ s i : ℝ)) (m : NNReal)) := by
        -- Split the transport sum into the distinguished singleton and the tail.
        rw [Finsupp.sum_add_index]
        · simp
        · simp
        · intro s a b₁ b₂
          ext t
          simp [NNReal.coe_add]
      -- Rewrite both the transported assignment and the translated integer sum by splitting off
      -- the distinguished singleton term.
      rw [hsum, ← add_assoc, Finsupp.sum_add_index]
      · have htail :
            (x.sum (fun s m ↦ Finsupp.single (fun i ↦ s i + (σ s i : ℝ)) (m : NNReal))).sum
                (fun s a ↦ ψ s * (a : ℝ)) =
              x.sum (fun s m ↦ ψ (fun i ↦ s i + (σ s i : ℝ)) * (m : ℝ)) := by
          simpa using ih (y := 0)
        have hhead :
            (y + Finsupp.single (fun i ↦ r i + (σ r i : ℝ)) (n : NNReal)).sum
                (fun s a ↦ ψ s * (a : ℝ)) =
              y.sum (fun s a ↦ ψ s * (a : ℝ)) +
                ψ (fun i ↦ r i + (σ r i : ℝ)) * (n : ℝ) := by
          rw [Finsupp.sum_add_index]
          · simp
          · intro s
            simp
          · intro s a b₁ b₂
            simp [NNReal.coe_add, left_distrib]
        have hrhs :
            (Finsupp.single r n + x).sum
                (fun s m ↦ ψ (fun i ↦ s i + (σ s i : ℝ)) * (m : ℝ)) =
              ψ (fun i ↦ r i + (σ r i : ℝ)) * (n : ℝ) +
                x.sum (fun s m ↦ ψ (fun i ↦ s i + (σ s i : ℝ)) * (m : ℝ)) := by
          rw [Finsupp.sum_add_index]
          · simp
          · intro s
            simp
          · intro s a b₁ b₂
            simp [Nat.cast_add, left_distrib]
        rw [hhead, htail, hrhs]
        ring
      · intro s
        simp
      · intro s a b₁ b₂
        simp [NNReal.coe_add, left_distrib]

/-- Helper for Remark 6.36: the trivial lifting satisfies the mixed cut inequality whenever `ψ`
is valid for the continuous relaxation `R_f`. -/
lemma trivialLiftingOneLeOfContinuousValid
    {f : Rq}
    {ψ : Rq → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ)
    {x : NatAssignment}
    {y : ContAssignment}
    (hxy : (x, y) ∈ mixed_integer_relaxation_set f) :
    1 ≤
      x.sum (fun r n ↦ trivial_lifting ψ r * (n : ℝ)) +
        y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
  -- Route correction: prove the global mixed inequality directly by transporting all integer mass
  -- to the continuous side, instead of isolating a pointwise negative branch first.
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  rcases existsTranslateChoiceWeightedApprox ψ x hε with ⟨σ, happrox⟩
  let yσ : ContAssignment :=
    y + x.sum (fun r n ↦ Finsupp.single (fun i ↦ r i + (σ r i : ℝ)) (n : NNReal))
  have hyσ :
      yσ ∈ continuous_infinite_relaxation_feasible_set f := by
    exact transportIntegerMassToContinuousFeasible (σ := σ) hxy
  have hbase :
      1 ≤ yσ.sum (fun r a ↦ ψ r * (a : ℝ)) :=
    continuous_infinite_valid_function_one_le hψ hyσ
  have hyσsum :
      yσ.sum (fun r a ↦ ψ r * (a : ℝ)) =
        y.sum (fun r a ↦ ψ r * (a : ℝ)) +
          x.sum (fun r n ↦ ψ (fun i ↦ r i + (σ r i : ℝ)) * (n : ℝ)) := by
    -- Rewrite the transported continuous sum into the original continuous part plus the chosen
    -- translated integer contribution.
    simpa [yσ] using transportedContinuousAssignmentCutSum ψ σ x y
  have hbase' :
      1 ≤
        y.sum (fun r a ↦ ψ r * (a : ℝ)) +
          x.sum (fun r n ↦ ψ (fun i ↦ r i + (σ r i : ℝ)) * (n : ℝ)) := by
    simpa [hyσsum] using hbase
  calc
    1 ≤
        y.sum (fun r a ↦ ψ r * (a : ℝ)) +
          x.sum (fun r n ↦ ψ (fun i ↦ r i + (σ r i : ℝ)) * (n : ℝ)) := hbase'
    _ ≤
        y.sum (fun r a ↦ ψ r * (a : ℝ)) +
          (x.sum (fun r n ↦ trivial_lifting ψ r * (n : ℝ)) + ε) := by
            linarith
    _ =
        x.sum (fun r n ↦ trivial_lifting ψ r * (n : ℝ)) +
          y.sum (fun r a ↦ ψ r * (a : ℝ)) + ε := by
            ring

/-- Helper for Remark 6.36: the ceiling correction coefficient at coordinate `i` is nonnegative,
so it defines a valid `NNReal` mass on the `i`-th standard basis vector. -/
lemma ceilingBasisCorrectionCoeffNonneg
    (f r : Rq)
    (M : ℕ)
    (i : Fin q) :
    0 ≤ (Int.ceil (f i + (M : ℝ) * r i) : ℝ) - (f i + (M : ℝ) * r i) := by
  -- The ceiling lies above the original coordinate, so the correction is nonnegative.
  exact sub_nonneg.mpr (Int.le_ceil (f i + (M : ℝ) * r i))

/-- Helper for Remark 6.36: the bounded ceiling correction added at the `i`-th standard basis
vector when making `f + (M : ℝ) • r` integral. -/
def ceilingBasisCorrectionCoeff
    (f r : Rq)
    (M : ℕ)
    (i : Fin q) : NNReal :=
  ⟨(Int.ceil (f i + (M : ℝ) * r i) : ℝ) - (f i + (M : ℝ) * r i),
    ceilingBasisCorrectionCoeffNonneg f r M i⟩

/-- The real value of the ceiling correction coefficient is its defining difference
`⌈f i + M * r i⌉ - (f i + M * r i)`. -/
@[simp] theorem ceilingBasisCorrectionCoeff_coe
    (f r : Rq)
    (M : ℕ)
    (i : Fin q) :
    ((ceilingBasisCorrectionCoeff f r M i : NNReal) : ℝ) =
      (Int.ceil (f i + (M : ℝ) * r i) : ℝ) - (f i + (M : ℝ) * r i) :=
  rfl

/-- Helper for Remark 6.36: every ceiling correction coefficient is at most `1`. -/
lemma ceilingBasisCorrectionCoeff_le_one
    (f r : Rq)
    (M : ℕ)
    (i : Fin q) :
    ((ceilingBasisCorrectionCoeff f r M i : NNReal) : ℝ) ≤ 1 := by
  -- The gap from a real number to its ceiling is always bounded by `1`.
  have hceil_lt :
      (Int.ceil (f i + (M : ℝ) * r i) : ℝ) <
        (f i + (M : ℝ) * r i) + 1 := by
    exact Int.ceil_lt_add_one (f i + (M : ℝ) * r i)
  rw [ceilingBasisCorrectionCoeff_coe]
  linarith

/-- Helper for Remark 6.36: the bounded basis-correction assignment used to make
`f + (M : ℝ) • r` integral. -/
def ceilingBasisCorrectionAssignment
    (f r : Rq)
    (M : ℕ) : ContAssignment :=
  Finsupp.single r (M : NNReal) +
    Finset.univ.sum
      (fun i : Fin q ↦
        Finsupp.single (Pi.single i (1 : ℝ)) (ceilingBasisCorrectionCoeff f r M i))

/-- Helper for Remark 6.36: summing standard-basis singletons and then taking their weighted
vector sum reproduces the expected linear combination of basis vectors. -/
lemma standardBasisSingletonsVectorSum
    (δ : Fin q → NNReal)
    (s : Finset (Fin q)) :
    (∑ i ∈ s, Finsupp.single (Pi.single i (1 : ℝ)) (δ i)).sum
        (fun r a ↦ (a : ℝ) • r) =
      ∑ i ∈ s, ((δ i : NNReal) : ℝ) • Pi.single i (1 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty family contributes no mass to either side.
      simp
  | @insert i s hi ih =>
      -- Split off one basis singleton and reassemble the tail with the induction hypothesis.
      rw [Finset.sum_insert hi, Finsupp.sum_add_index, ih, Finset.sum_insert hi]
      · simp
      · intro r
        simp
      · intro r a b
        simp [NNReal.coe_add, add_smul]

/-- Helper for Remark 6.36: summing standard-basis singletons and then evaluating the cut defined
by `ψ` reproduces the expected finite weighted basis sum. -/
lemma standardBasisSingletonsCutSum
    (ψ : Rq → ℝ)
    (δ : Fin q → NNReal)
    (s : Finset (Fin q)) :
    (∑ i ∈ s, Finsupp.single (Pi.single i (1 : ℝ)) (δ i)).sum
        (fun r a ↦ ψ r * (a : ℝ)) =
      ∑ i ∈ s, ψ (Pi.single i (1 : ℝ)) * ((δ i : NNReal) : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty family contributes no cut value.
      simp
  | @insert i s hi ih =>
      -- Split off one basis singleton and reassemble the tail with the induction hypothesis.
      rw [Finset.sum_insert hi, Finsupp.sum_add_index, ih, Finset.sum_insert hi]
      · simp
      · intro r
        simp
      · intro r a b
        simp [NNReal.coe_add, left_distrib]

/-- Helper for Remark 6.36: the basis-correction assignment has vector sum
`(M : ℝ) • r + ∑ i, δ_i e_i`, where `δ_i` is the ceiling correction at coordinate `i`. -/
lemma ceilingBasisCorrectionAssignmentVectorSum
    (f r : Rq)
    (M : ℕ) :
    (ceilingBasisCorrectionAssignment f r M).sum (fun s a ↦ (a : ℝ) • s) =
      (M : ℝ) • r +
        (fun i ↦ ((ceilingBasisCorrectionCoeff f r M i : NNReal) : ℝ)) := by
  have hsingle :
      (Finsupp.single r (M : NNReal)).sum (fun s a ↦ (a : ℝ) • s) =
        (M : ℝ) • r := by
    -- The singleton at `r` contributes exactly `(M : ℝ) • r`.
    simp
  have hbasis :
      (Finset.univ.sum
          (fun i : Fin q ↦
            Finsupp.single (Pi.single i (1 : ℝ))
              (ceilingBasisCorrectionCoeff f r M i))).sum
          (fun s a ↦ (a : ℝ) • s) =
        ∑ i : Fin q,
          ((ceilingBasisCorrectionCoeff f r M i : NNReal) : ℝ) •
            Pi.single i (1 : ℝ) := by
    -- The basis part linearizes to the expected weighted basis-vector combination.
    simpa using
      standardBasisSingletonsVectorSum
        (δ := ceilingBasisCorrectionCoeff f r M) (s := Finset.univ)
  have hbasis' :
      (∑ i : Fin q,
          ((ceilingBasisCorrectionCoeff f r M i : NNReal) : ℝ) •
            Pi.single i (1 : ℝ)) =
        (fun i ↦ ((ceilingBasisCorrectionCoeff f r M i : NNReal) : ℝ)) := by
    -- Summing the weighted standard basis vectors reconstructs the correction vector.
    funext j
    simp [Pi.smul_apply, Pi.single_apply]
  rw [ceilingBasisCorrectionAssignment, Finsupp.sum_add_index]
  · rw [hsingle, hbasis, hbasis']
  · intro s
    simp
  · intro s a b
    simp [NNReal.coe_add, add_smul]

/-- Helper for Remark 6.36: the ceiling-corrected assignment is feasible for the continuous
infinite relaxation `R_f`. -/
lemma ceilingBasisCorrectionFeasible
    {f : Rq}
    (r : Rq)
    (M : ℕ) :
    ceilingBasisCorrectionAssignment f r M ∈ continuous_infinite_relaxation_feasible_set f := by
  rw [mem_continuous_infinite_relaxation_feasible_set_iff]
  refine ⟨fun i ↦ Int.ceil (f i + (M : ℝ) * r i), ?_⟩
  -- Normalize the balance vector through the explicit basis-correction decomposition.
  ext i
  rw [continuous_infinite_balance, ceilingBasisCorrectionAssignmentVectorSum, Pi.add_apply,
    Pi.add_apply, Pi.smul_apply]
  rw [ceilingBasisCorrectionCoeff_coe]
  have hcoord :
      (Int.ceil (f i + (M : ℝ) * r i) : ℝ) =
        f i + ((M : ℝ) * r i +
          ((Int.ceil (f i + (M : ℝ) * r i) : ℝ) - (f i + (M : ℝ) * r i))) := by
    ring
  simpa [Function.comp, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using hcoord

/-- Helper for Remark 6.36: the cut value of the ceiling-corrected assignment is the affine term
`ψ r * M` plus the finite basis-correction contribution. -/
lemma ceilingBasisCorrectionCutSum
    {f : Rq}
    (ψ : Rq → ℝ)
    (r : Rq)
    (M : ℕ) :
    (ceilingBasisCorrectionAssignment f r M).sum (fun s a ↦ ψ s * (a : ℝ)) =
      ψ r * (M : ℝ) +
        ∑ i : Fin q,
          ψ (Pi.single i (1 : ℝ)) *
            ((ceilingBasisCorrectionCoeff f r M i : NNReal) : ℝ) := by
  have hsingle :
      (Finsupp.single r (M : NNReal)).sum (fun s a ↦ ψ s * (a : ℝ)) =
        ψ r * (M : ℝ) := by
    -- The singleton at `r` contributes exactly the slope term `ψ r * M`.
    simp
  have hbasis :
      (Finset.univ.sum
          (fun i : Fin q ↦
            Finsupp.single (Pi.single i (1 : ℝ))
              (ceilingBasisCorrectionCoeff f r M i))).sum
          (fun s a ↦ ψ s * (a : ℝ)) =
        ∑ i : Fin q,
          ψ (Pi.single i (1 : ℝ)) *
            ((ceilingBasisCorrectionCoeff f r M i : NNReal) : ℝ) := by
    -- The basis part linearizes to the expected finite correction sum.
    simpa using
      standardBasisSingletonsCutSum
        (ψ := ψ) (δ := ceilingBasisCorrectionCoeff f r M) (s := Finset.univ)
  rw [ceilingBasisCorrectionAssignment, Finsupp.sum_add_index]
  · rw [hsingle, hbasis]
  · intro s
    simp
  · intro s a b
    simp [NNReal.coe_add, left_distrib]

/-- Helper for Remark 6.36: a continuous-valid function is nonnegative on each standard basis
vector. -/
lemma continuousValidFunctionNonnegOnStandardBasis
    {f : Rq}
    {ψ : Rq → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ)
    (i : Fin q) :
    0 ≤ ψ (Pi.single i (1 : ℝ)) := by
  let e : Fin q → ℚ := fun j ↦ if j = i then (1 : ℚ) else 0
  have hrational :
      0 ≤ ψ (fun j ↦ (e j : ℝ)) :=
    continuousInfiniteValidFunctionNonnegOnRationalVectors
      (f := f) (ψ := ψ) hψ e
  have he :
      (fun j ↦ (e j : ℝ)) = Pi.single i (1 : ℝ) := by
    -- The chosen rational vector is exactly the `i`-th standard basis vector after casting.
    funext j
    by_cases hji : j = i
    · subst hji
      simp [e]
    · simp [e, hji]
  simpa [he] using hrational

/-- Helper for Remark 6.36: every valid function for the continuous infinite relaxation is
pointwise nonnegative. -/
lemma continuousValidFunctionNonnegative
    {f : Rq}
    {ψ : Rq → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ)
    (r : Rq) :
    0 ≤ ψ r := by
  by_contra hnonneg
  have hneg : ψ r < 0 := lt_of_not_ge hnonneg
  let C : ℝ := ∑ i : Fin q, ψ (Pi.single i (1 : ℝ))
  obtain ⟨M, hM⟩ :=
    exists_nat_cutViolation_of_negativeSlope
      (a := C) (b := ψ r) (D := 1) hneg (by norm_num)
  have hfeasible :
      ceilingBasisCorrectionAssignment f r M ∈
        continuous_infinite_relaxation_feasible_set f :=
    ceilingBasisCorrectionFeasible (f := f) (r := r) M
  have hvalid :
      1 ≤
        (ceilingBasisCorrectionAssignment f r M).sum
          (fun s a ↦ ψ s * (a : ℝ)) :=
    continuous_infinite_valid_function_one_le hψ hfeasible
  rw [ceilingBasisCorrectionCutSum (f := f) (ψ := ψ) (r := r) (M := M)] at hvalid
  have hcorr_le :
      (∑ i : Fin q,
          ψ (Pi.single i (1 : ℝ)) *
            ((ceilingBasisCorrectionCoeff f r M i : NNReal) : ℝ)) ≤ C := by
    -- Each correction coefficient lies in `[0, 1]`, so the total correction is bounded by the
    -- fixed sum of basis values of `ψ`.
    dsimp [C]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hψi_nonneg : 0 ≤ ψ (Pi.single i (1 : ℝ)) :=
      continuousValidFunctionNonnegOnStandardBasis hψ i
    calc
      ψ (Pi.single i (1 : ℝ)) *
          ((ceilingBasisCorrectionCoeff f r M i : NNReal) : ℝ) ≤
        ψ (Pi.single i (1 : ℝ)) * 1 := by
          exact mul_le_mul_of_nonneg_left
            (ceilingBasisCorrectionCoeff_le_one f r M i) hψi_nonneg
      _ = ψ (Pi.single i (1 : ℝ)) := by ring
  have hvalid' : 1 ≤ ψ r * (M : ℝ) + C := by
    linarith
  have hcut_lt : C + ψ r * (M : ℝ) < 1 := by
    -- Choose `M` so that the negative slope at `r` eventually forces the affine expression below
    -- `1`.
    simpa [C, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hM
  linarith

/-- Helper for Remark 6.36: the trivial lifting is pointwise nonnegative because every integer
translate of a continuous-valid function is nonnegative. -/
lemma trivialLiftingNonnegativeOfContinuousValid
    {f : Rq}
    {ψ : Rq → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ)
    (r : Rq) :
    0 ≤ trivial_lifting ψ r := by
  rw [trivial_lifting_apply]
  refine le_csInf ?_ ?_
  · -- The translate set is nonempty, for instance by taking the zero integer vector.
    exact ⟨_, ⟨0, rfl⟩⟩
  · intro t ht
    rcases ht with ⟨w, rfl⟩
    -- Every translate is another point of `ℝ^q`, so the global nonnegativity theorem applies.
    exact continuousValidFunctionNonnegative hψ (fun i ↦ r i + (w i : ℝ))

/-- Helper for Remark 6.36: if `ψ` is valid for `R_f`, then the trivial lifting satisfies the
mixed-integer validity inequality and should therefore be viewed as the canonical lifting
candidate. -/
theorem trivialLiftingIsLiftingOfContinuousValid
    {f : Rq}
    {ψ : Rq → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ) :
    IsValidGomoryJohnsonPair f (trivial_lifting ψ) ψ := by
  refine
    { nonneg := ?_
      one_le := ?_ }
  · intro r
    -- The infimum of the nonnegative translate values is itself nonnegative.
    exact trivialLiftingNonnegativeOfContinuousValid hψ r
  · intro x y hxy
    -- The global transport route already proves the mixed cut inequality.
    exact trivialLiftingOneLeOfContinuousValid hψ hxy

/-- If `ψ` admits a minimal lifting, then `trivial_lifting ψ` is pointwise nonnegative. -/
lemma trivialLiftingNonnegativeOfExistsMinimal
    {f : Rq}
    {ψ : Rq → ℝ}
    (hexists : ∃ π : Rq → ℝ, IsMinimalLiftingOf f π ψ)
    (r : Rq) :
    0 ≤ trivial_lifting ψ r := by
  rcases hexists with ⟨π, hπ⟩
  -- Defer the pointwise nonnegativity to the direct validity theorem for the trivial lifting.
  exact
    (trivialLiftingIsLiftingOfContinuousValid
      (hψ := IsValidGomoryJohnsonPair.toContinuousValidFunction
        hπ.toIsValidGomoryJohnsonPair)).nonneg r

/-- Helper for Remark 6.36: every minimal lifting `π` of a valid function `ψ` is pointwise bounded
above by the trivial lifting of `ψ`. -/
theorem minimal_lifting_le_trivial_lifting
    (f : Rq)
    (ψ π : Rq → ℝ)
    (hπ : IsMinimalLiftingOf f π ψ) :
    π ≤ trivial_lifting ψ := by
  intro r
  by_contra hlt
  -- Route correction: use an intermediate nonnegative coefficient in the nonnegative branch, and
  -- leave the genuinely hard negative branch isolated in the dedicated nonnegativity lemma.
  by_cases htrivial_nonneg : 0 ≤ trivial_lifting ψ r
  · have hstrict : trivial_lifting ψ r < π r :=
      lt_of_not_ge hlt
    rcases existsUpperBoundBetweenTrivialAndPi r htrivial_nonneg hstrict with
      ⟨a, ha_nonneg, htrivial_le, ha_lt⟩
    let ρ : Rq → ℝ := fun s ↦ if s = r then a else π s
    have hρvalid : IsValidGomoryJohnsonPair f ρ ψ :=
      replaceAtWithTrivialLiftingBoundValid hπ.toIsValidGomoryJohnsonPair r a ha_nonneg htrivial_le
    have hle : ρ ≤ π := by
      intro s
      by_cases hs : s = r
      · -- At the distinguished column, the midpoint coefficient is strictly smaller than `π r`.
        simpa [ρ, hs] using le_of_lt ha_lt
      · -- Away from `r`, the replacement leaves the lifting unchanged.
        simp [ρ, hs]
    have heq := hπ.eq_of_le hρvalid hle
    have hpoint := congrArg (fun τ : Rq → ℝ ↦ τ r) heq
    have hr_eq : a = π r := by
      simpa [ρ] using hpoint
    linarith
  · -- The negative branch is the remaining structural content: it is ruled out by the dedicated
    -- nonnegativity lemma for the trivial lifting.
    exact htrivial_nonneg (trivialLiftingNonnegativeOfExistsMinimal ⟨π, hπ⟩ r)

/-- Helper for Remark 6.36: if `ψ` admits a minimal lifting, then `trivial_lifting ψ` is itself a
valid Gomory--Johnson lifting of `ψ`. -/
theorem trivialLiftingIsLiftingOfExistsMinimal
    {f : Rq}
    {ψ : Rq → ℝ}
    (hexists : ∃ π : Rq → ℝ, IsMinimalLiftingOf f π ψ) :
    IsValidGomoryJohnsonPair f (trivial_lifting ψ) ψ := by
  rcases hexists with ⟨π, hπ⟩
  -- The existence hypothesis is only used to recover continuous validity of `ψ`.
  simpa using
    (trivialLiftingIsLiftingOfContinuousValid
      (hψ := IsValidGomoryJohnsonPair.toContinuousValidFunction hπ.toIsValidGomoryJohnsonPair))

/-- Remark 6.36. If `ψ` is a valid function for `R_f`, then the trivial lifting of `ψ` is itself a
lifting of `ψ`. -/
theorem trivial_lifting_is_lifting
    (f : Rq)
    (ψ : Rq → ℝ)
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ) :
    IsValidGomoryJohnsonPair f (trivial_lifting ψ) ψ := by
  simpa using trivialLiftingIsLiftingOfContinuousValid (f := f) (ψ := ψ) hψ

section OneDimensional

local notation "R1" => Fin 1 → ℝ

/-- The one-dimensional valid Gomory--Johnson pair owner is the `q = 1` specialization of the
chapter's canonical mixed-integer valid-pair owner. -/
abbrev IsValidGomoryJohnsonPairOnR (f : ℝ) (π ψ : ℝ → ℝ) : Prop :=
  IsValidGomoryJohnsonPair (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ π (r 0)) (fun r : R1 ↦ ψ (r 0))

/-- The one-dimensional minimal-lifting owner is the `q = 1` specialization of the chapter's
canonical minimal-lifting owner. -/
abbrev IsMinimalLiftingOfOnR (f : ℝ) (π ψ : ℝ → ℝ) : Prop :=
  IsMinimalLiftingOf (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ π (r 0)) (fun r : R1 ↦ ψ (r 0))

/-- The one-dimensional trivial lifting is the `q = 1` specialization of the chapter's canonical
trivial-lifting construction. -/
def trivial_lifting_on_R (ψ : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦ trivial_lifting (fun s : R1 ↦ ψ (s 0)) (fun _ ↦ r)

/-- Unfolding the one-dimensional valid-pair owner recovers the canonical `q = 1` chapter owner.
-/
theorem isValidGomoryJohnsonPairOnR_iff {f : ℝ} {π ψ : ℝ → ℝ} :
    IsValidGomoryJohnsonPairOnR f π ψ ↔
      IsValidGomoryJohnsonPair
        (fun _ : Fin 1 ↦ f)
        (fun r : R1 ↦ π (r 0))
        (fun r : R1 ↦ ψ (r 0)) :=
  Iff.rfl

/-- Unfolding the one-dimensional minimal-lifting owner recovers the canonical `q = 1` chapter
owner. -/
theorem isMinimalLiftingOfOnR_iff {f : ℝ} {π ψ : ℝ → ℝ} :
    IsMinimalLiftingOfOnR f π ψ ↔
      IsMinimalLiftingOf
        (fun _ : Fin 1 ↦ f)
        (fun r : R1 ↦ π (r 0))
        (fun r : R1 ↦ ψ (r 0)) :=
  Iff.rfl

/-- Evaluating `trivial_lifting_on_R ψ` at `r` recovers the canonical `q = 1` trivial lifting
through the scalar-to-vector bridge. -/
@[simp] theorem trivial_lifting_on_R_apply
    (ψ : ℝ → ℝ)
    (r : ℝ) :
    trivial_lifting_on_R ψ r =
      trivial_lifting (fun s : R1 ↦ ψ (s 0)) (fun _ ↦ r) :=
  rfl

/-- A one-dimensional minimal lifting on `ℝ` is a one-dimensional valid Gomory--Johnson pair. -/
instance instIsValidGomoryJohnsonPairOnROfMinimal
    {f : ℝ} {π ψ : ℝ → ℝ} [hπ : IsMinimalLiftingOfOnR f π ψ] :
    IsValidGomoryJohnsonPairOnR f π ψ :=
  hπ.toIsValidGomoryJohnsonPair

/-- Minimality on `ℝ` can be used through pointwise domination among one-dimensional valid
Gomory--Johnson pairs. -/
theorem isMinimalLiftingOfOnR_eq_of_le
    {f : ℝ} {π π' ψ : ℝ → ℝ}
    (hπ : IsMinimalLiftingOfOnR f π ψ)
    (hπ' : IsValidGomoryJohnsonPairOnR f π' ψ)
    (hle : ∀ r : ℝ, π' r ≤ π r) :
    π' = π := by
  have hle' : ∀ r : R1, π' (r 0) ≤ π (r 0) := fun r ↦ hle (r 0)
  have hEq : (fun r : R1 ↦ π' (r 0)) = fun r : R1 ↦ π (r 0) :=
    hπ.eq_of_le hπ' hle'
  ext r
  exact congrFun hEq (fun _ ↦ r)

end OneDimensional

end Remark636
