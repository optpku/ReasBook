/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_4.ch10_sec10_4_1_proposition_10_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SheraliAdamsNotation

-- Source/core/bridge triage for this file:
-- * `source-facing`: Claim 1 conditions the subset-moment vector `widehat y` by fixing one
--   variable, starting from a Step-2 presentation of `R_{t - 1}(P)`.
-- * `core/canonical`: Proposition 10.12 already owns the Sherali-Adams relaxation `R_t` with
--   owner `sherali_adams_relaxation` and scoped notation `R_{t}(P)`.
-- * `bridge/view`: a Step-2 presentation exposes the coefficient families cutting out
--   `R_{t - 1}(P)`, and Claim 1 sends their lifted inequalities to the conditioned vectors.
--
-- Accordingly, this file keeps the conditioning formulas, packages the source-facing Step-2
-- presentation of `R_t(P)`, and states Claim 1 directly as a bridge from that presentation into
-- the canonical owner `R_{t}(P)`.

section Claim1

variable {n t : ℕ}

namespace SheraliAdams
namespace Conditioning

/-- A coefficient family indexing one linearized Sherali-Adams inequality. -/
abbrev CoeffFamily (n : ℕ) := Finset (Fin n) → ℝ

/-- The value of a linearized Sherali-Adams inequality on a moment vector. -/
def linearFormEval
    (c y : CoeffFamily n) : ℝ :=
  Finset.sum ((Finset.univ : Finset (Fin n)).powerset) (fun S ↦ c S * y S)

/-- A Step-2 presentation of `R_{t}(P)` by coefficient families whose nonnegative linear forms cut
out the relaxation. -/
structure StepInequalityPresentation
    (P : Set (Fin n → ℝ))
    (t : ℕ) where
  inequalities : Set (CoeffFamily n)
  mem_relaxation_iff' :
    ∀ y : CoeffFamily n, y ∈ R_{t}(P) ↔ ∀ c ∈ inequalities, 0 ≤ linearFormEval c y

namespace StepInequalityPresentation

variable {P : Set (Fin n → ℝ)} {t : ℕ}

/-- A moment vector satisfies a Step-2 presentation when it satisfies every inequality in the
presenting family. -/
def Satisfies
    (presentation : StepInequalityPresentation P t)
    (y : CoeffFamily n) : Prop :=
  ∀ c ∈ presentation.inequalities, 0 ≤ linearFormEval c y

/-- `presentation.Satisfies y` is exactly the pointwise nonnegativity of its presenting
coefficient families. -/
@[simp] theorem satisfies_iff
    (presentation : StepInequalityPresentation P t)
    (y : CoeffFamily n) :
    presentation.Satisfies y ↔
      ∀ c ∈ presentation.inequalities, 0 ≤ linearFormEval c y :=
  Iff.rfl

/-- A Step-2 presentation exposes membership in `R_{t}(P)` as satisfaction of its inequalities. -/
@[simp] theorem mem_relaxation_iff
    (presentation : StepInequalityPresentation P t)
    (y : CoeffFamily n) :
    y ∈ R_{t}(P) ↔ presentation.Satisfies y :=
  presentation.mem_relaxation_iff' y

end StepInequalityPresentation

/-- The conditioned vector `onOne widehat_y h` obtained from `widehat_y` by fixing the variable
`x_h = 1`. Its coordinates are
`onOne widehat_y h S = widehat_y ({h} : Finset (Fin n))⁻¹ * widehat_y (insert h S)`. -/
noncomputable def onOne
    (widehat_y : CoeffFamily n) (h : Fin n) : CoeffFamily n :=
  fun S ↦ (widehat_y ({h} : Finset (Fin n)))⁻¹ * widehat_y (insert h S)

/-- `onOne widehat_y h` is given coordinatewise by the conditioning rule for `x_h = 1`. -/
@[simp] theorem onOne_apply
    (widehat_y : CoeffFamily n) (h : Fin n) (S : Finset (Fin n)) :
    onOne widehat_y h S =
      (widehat_y ({h} : Finset (Fin n)))⁻¹ * widehat_y (insert h S) :=
  rfl

/-- The conditioned vector `onZero widehat_y h` obtained from `widehat_y` by fixing the variable
`x_h = 0`. Its coordinates are
`onZero widehat_y h S =
  (1 - widehat_y ({h} : Finset (Fin n)))⁻¹ * (widehat_y S - widehat_y (insert h S))`. -/
noncomputable def onZero
    (widehat_y : CoeffFamily n) (h : Fin n) : CoeffFamily n :=
  fun S ↦
    (1 - widehat_y ({h} : Finset (Fin n)))⁻¹ *
      (widehat_y S - widehat_y (insert h S))

/-- `onZero widehat_y h` is given coordinatewise by the conditioning rule for `x_h = 0`. -/
@[simp] theorem onZero_apply
    (widehat_y : CoeffFamily n) (h : Fin n) (S : Finset (Fin n)) :
    onZero widehat_y h S =
      (1 - widehat_y ({h} : Finset (Fin n)))⁻¹ *
        (widehat_y S - widehat_y (insert h S)) :=
  rfl

/-- The coefficient family obtained by multiplying a Step-2 inequality with `x_h`, as described
in Claim 1. -/
def liftOnOne
    (c : CoeffFamily n)
    (h : Fin n) : CoeffFamily n :=
  fun S ↦ if h ∈ S then c S + c (S.erase h) else 0

/-- `liftOnOne c h` is given by the coefficient rule induced by multiplying by `x_h`. -/
@[simp] theorem liftOnOne_apply
    (c : CoeffFamily n)
    (h : Fin n)
    (S : Finset (Fin n)) :
    liftOnOne c h S =
      if h ∈ S then c S + c (S.erase h) else 0 :=
  rfl

/-- The coefficient family obtained by multiplying a Step-2 inequality with `1 - x_h`, as used
for `onZero widehat_y h` in Claim 1. -/
def liftOnZero
    (c : CoeffFamily n)
    (h : Fin n) : CoeffFamily n :=
  fun S ↦ if h ∈ S then -c (S.erase h) else c S

/-- `liftOnZero c h` is given by the coefficient rule for the lift by `1 - x_h`. -/
@[simp] theorem liftOnZero_apply
    (c : CoeffFamily n)
    (h : Fin n)
    (S : Finset (Fin n)) :
    liftOnZero c h S =
      if h ∈ S then -c (S.erase h) else c S :=
  rfl

end Conditioning
end SheraliAdams

open SheraliAdams.Conditioning

/-- Helper for Claim 1: split `linearFormEval c y` into subsets omitting `h` and subsets obtained
by inserting `h` into a subset of `Finset.univ.erase h`. -/
theorem linearFormEval_splitAtSingleton
    (c y : CoeffFamily n)
    (h : Fin n) :
    linearFormEval c y =
      Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset) (fun S ↦ c S * y S)
        + Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
            (fun S ↦ c (insert h S) * y (insert h S)) := by
  -- Split the powerset of `Finset.univ` using the distinguished singleton `{h}`.
  unfold linearFormEval
  rw [← Finset.insert_erase (s := (Finset.univ : Finset (Fin n))) (a := h) (by simp)]
  simpa using
    (Finset.sum_powerset_insert
      (s := ((Finset.univ : Finset (Fin n)).erase h))
      (a := h)
      (ha := by simp)
      (f := fun S ↦ c S * y S))

/-- Helper for Claim 1: once `h` is already present in the index set, the `onZero` conditioning
coordinate vanishes. -/
theorem onZero_apply_insert
    (widehat_y : CoeffFamily n)
    (h : Fin n)
    (S : Finset (Fin n))
    (hhS : h ∉ S) :
    onZero widehat_y h (insert h S) = 0 := by
  -- The numerator cancels because inserting `h` twice does not change the set.
  simp [onZero_apply, hhS]

/-- Helper for Claim 1: evaluating an inequality on `onOne widehat_y h` is the inverse singleton
coordinate times the lifted inequality evaluated on `widehat_y`. -/
theorem linearFormEval_onOne_eq_inv_mul_liftOnOne
    (c widehat_y : CoeffFamily n)
    (h : Fin n) :
    linearFormEval c (onOne widehat_y h) =
      (widehat_y ({h} : Finset (Fin n)))⁻¹ *
        linearFormEval (liftOnOne c h) widehat_y := by
  have hLift :
      linearFormEval (liftOnOne c h) widehat_y =
        Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
          (fun S ↦ (liftOnOne c h) (insert h S) * widehat_y (insert h S)) := by
    -- The lift by `x_h` contributes only on subsets that already contain `h`.
    rw [linearFormEval_splitAtSingleton (c := liftOnOne c h) (y := widehat_y) (h := h)]
    have hZero :
        Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
          (fun S ↦ liftOnOne c h S * widehat_y S) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro S hS
      have hhS : h ∉ S :=
        Finset.notMem_of_mem_powerset_of_notMem hS (by simp)
      simp [liftOnOne_apply, hhS]
    rw [hZero, zero_add]
  have hSummand :
      ∀ S ∈ (((Finset.univ : Finset (Fin n)).erase h).powerset),
        c S * onOne widehat_y h S + c (insert h S) * onOne widehat_y h (insert h S) =
          (widehat_y ({h} : Finset (Fin n)))⁻¹ *
            ((liftOnOne c h) (insert h S) * widehat_y (insert h S)) := by
    intro S hS
    have hhS : h ∉ S :=
      Finset.notMem_of_mem_powerset_of_notMem hS (by simp)
    simp [onOne_apply, liftOnOne_apply, hhS, mul_add, add_mul, mul_assoc, mul_comm, add_comm]
  -- Rewrite both halves of the split sum using the conditioning formula for `onOne`.
  calc
    linearFormEval c (onOne widehat_y h)
      =
        Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
          (fun S ↦
            c S * onOne widehat_y h S + c (insert h S) * onOne widehat_y h (insert h S)) := by
            rw [linearFormEval_splitAtSingleton (c := c) (y := onOne widehat_y h) (h := h)]
            rw [← Finset.sum_add_distrib]
    _ =
        Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
          (fun S ↦
            (widehat_y ({h} : Finset (Fin n)))⁻¹ *
              ((liftOnOne c h) (insert h S) * widehat_y (insert h S))) := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            exact hSummand S hS
    _ =
        (widehat_y ({h} : Finset (Fin n)))⁻¹ *
          Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
            (fun S ↦ (liftOnOne c h) (insert h S) * widehat_y (insert h S)) := by
            rw [Finset.mul_sum]
    _ = (widehat_y ({h} : Finset (Fin n)))⁻¹ * linearFormEval (liftOnOne c h) widehat_y := by
          rw [hLift]

/-- Helper for Claim 1: evaluating an inequality on `onZero widehat_y h` is the inverse
denominator `1 - widehat_y {h}` times the lifted inequality evaluated on `widehat_y`. -/
theorem linearFormEval_onZero_eq_inv_mul_liftOnZero
    (c widehat_y : CoeffFamily n)
    (h : Fin n) :
    linearFormEval c (onZero widehat_y h) =
      (1 - widehat_y ({h} : Finset (Fin n)))⁻¹ *
        linearFormEval (liftOnZero c h) widehat_y := by
  have hLift :
      linearFormEval (liftOnZero c h) widehat_y =
        Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
          (fun S ↦ c S * widehat_y S + (-c S) * widehat_y (insert h S)) := by
    -- The split lift by `1 - x_h` gives the original term on `S` and `-c S` on `insert h S`.
    calc
      linearFormEval (liftOnZero c h) widehat_y
        =
          Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
            (fun S ↦ (liftOnZero c h) S * widehat_y S)
            + Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
                (fun S ↦ (liftOnZero c h) (insert h S) * widehat_y (insert h S)) := by
              rw [linearFormEval_splitAtSingleton (c := liftOnZero c h) (y := widehat_y) (h := h)]
      _ =
          Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
            (fun S ↦ c S * widehat_y S)
            + Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
                (fun S ↦ (-c S) * widehat_y (insert h S)) := by
              congr 1
              · refine Finset.sum_congr rfl ?_
                intro S hS
                have hhS : h ∉ S :=
                  Finset.notMem_of_mem_powerset_of_notMem hS (by simp)
                simp [liftOnZero_apply, hhS]
              · refine Finset.sum_congr rfl ?_
                intro S hS
                have hhS : h ∉ S :=
                  Finset.notMem_of_mem_powerset_of_notMem hS (by simp)
                simp [liftOnZero_apply, hhS]
      _ =
          Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
            (fun S ↦ c S * widehat_y S + (-c S) * widehat_y (insert h S)) := by
              rw [← Finset.sum_add_distrib]
  have hZero :
      Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
        (fun S ↦ c (insert h S) * onZero widehat_y h (insert h S)) = 0 := by
    -- The `h`-containing half vanishes for `onZero`.
    refine Finset.sum_eq_zero ?_
    intro S hS
    have hhS : h ∉ S :=
      Finset.notMem_of_mem_powerset_of_notMem hS (by simp)
    rw [onZero_apply_insert widehat_y h S hhS]
    simp
  have hSummand :
      ∀ S ∈ (((Finset.univ : Finset (Fin n)).erase h).powerset),
        c S * onZero widehat_y h S =
          (1 - widehat_y ({h} : Finset (Fin n)))⁻¹ *
            (c S * widehat_y S + (-c S) * widehat_y (insert h S)) := by
    intro S hS
    have hhS : h ∉ S :=
      Finset.notMem_of_mem_powerset_of_notMem hS (by simp)
    simp [onZero_apply, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_comm]
  calc
    linearFormEval c (onZero widehat_y h)
      =
        Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
          (fun S ↦ c S * onZero widehat_y h S) := by
            rw [linearFormEval_splitAtSingleton (c := c) (y := onZero widehat_y h) (h := h)]
            rw [hZero, add_zero]
    _ =
        Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
          (fun S ↦
            (1 - widehat_y ({h} : Finset (Fin n)))⁻¹ *
              (c S * widehat_y S + (-c S) * widehat_y (insert h S))) := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            exact hSummand S hS
    _ =
        (1 - widehat_y ({h} : Finset (Fin n)))⁻¹ *
          Finset.sum (((Finset.univ : Finset (Fin n)).erase h).powerset)
            (fun S ↦ c S * widehat_y S + (-c S) * widehat_y (insert h S)) := by
            rw [Finset.mul_sum]
    _ = (1 - widehat_y ({h} : Finset (Fin n)))⁻¹ * linearFormEval (liftOnZero c h) widehat_y := by
          rw [hLift]

/-- Claim 1 (bar `y`): if the lifts of all inequalities in a Step-2 presentation by `x_h` are
satisfied by `widehat_y`, and the conditioning denominator `widehat_y {h}` is nonnegative and
nonzero, then the conditioned vector `onOne widehat_y h` satisfies the original presentation. -/
theorem onOne_satisfiesStepInequalities
    {P : Set (Fin n → ℝ)} {t : ℕ}
    (presentation : StepInequalityPresentation P t)
    (widehat_y : CoeffFamily n)
    (h : Fin n)
    (hh_nonneg : 0 ≤ widehat_y ({h} : Finset (Fin n)))
    (hh_nonzero : widehat_y ({h} : Finset (Fin n)) ≠ 0)
    (hpositive :
      ∀ c ∈ presentation.inequalities, 0 ≤ linearFormEval (liftOnOne c h) widehat_y) :
    presentation.Satisfies (onOne widehat_y h) := by
  have _ : widehat_y ({h} : Finset (Fin n)) ≠ 0 := hh_nonzero
  -- Rewrite the conditioned evaluation as a nonnegative scalar multiple of the lifted inequality.
  intro c hc
  rw [linearFormEval_onOne_eq_inv_mul_liftOnOne]
  exact mul_nonneg (inv_nonneg.mpr hh_nonneg) (hpositive c hc)

/-- Claim 1 (tilde `y`): if the lifts of all inequalities in a Step-2 presentation by `1 - x_h`
are satisfied by `widehat_y`, and the conditioning denominator `1 - widehat_y {h}` is
nonnegative and nonzero, then the conditioned vector `onZero widehat_y h` satisfies the original
presentation. -/
theorem onZero_satisfiesStepInequalities
    {P : Set (Fin n → ℝ)} {t : ℕ}
    (presentation : StepInequalityPresentation P t)
    (widehat_y : CoeffFamily n)
    (h : Fin n)
    (hh_le_one : widehat_y ({h} : Finset (Fin n)) ≤ 1)
    (hh_ne_one : widehat_y ({h} : Finset (Fin n)) ≠ 1)
    (hnegative :
      ∀ c ∈ presentation.inequalities, 0 ≤ linearFormEval (liftOnZero c h) widehat_y) :
    presentation.Satisfies (onZero widehat_y h) := by
  have _ : widehat_y ({h} : Finset (Fin n)) ≠ 1 := hh_ne_one
  have hDenomNonneg : 0 ≤ 1 - widehat_y ({h} : Finset (Fin n)) :=
    sub_nonneg.mpr hh_le_one
  -- Rewrite the conditioned evaluation as a nonnegative scalar multiple of the lifted inequality.
  intro c hc
  rw [linearFormEval_onZero_eq_inv_mul_liftOnZero]
  exact mul_nonneg (inv_nonneg.mpr hDenomNonneg) (hnegative c hc)

/-- A nonzero singleton coordinate of a point in `R_{t}(P)` is automatically positive by
Proposition 10.12 (1). -/
theorem singleton_pos_of_mem_sherali_adams_relaxation_of_ne_zero
    {P : Set (Fin n → ℝ)} {t : ℕ}
    {widehat_y : CoeffFamily n}
    (hy : widehat_y ∈ R_{t}(P))
    (h : Fin n)
    (hh_nonzero : widehat_y ({h} : Finset (Fin n)) ≠ 0) :
    0 < widehat_y ({h} : Finset (Fin n)) := by
  exact lt_of_le_of_ne
    (sherali_adams_coordinate_nonneg hy (by simp))
    hh_nonzero.symm

/-- A singleton coordinate of a point in `R_{t}(P)` that is not equal to `1` is strictly less
than `1`, so the denominator in `onZero` is positive by Proposition 10.12 (3). -/
theorem singleton_lt_one_of_mem_sherali_adams_relaxation_of_ne_one
    {P : Set (Fin n → ℝ)} {t : ℕ}
    {widehat_y : CoeffFamily n}
    (hy : widehat_y ∈ R_{t}(P))
    (h : Fin n)
    (hh_ne_one : widehat_y ({h} : Finset (Fin n)) ≠ 1) :
    widehat_y ({h} : Finset (Fin n)) < 1 := by
  exact lt_of_le_of_ne
    (sherali_adams_coordinate_le_one hy (by simp))
    hh_ne_one

/-- If `widehat_y ∈ R_{t}(P)` and `widehat_y {h} ≠ 1`, then the denominator in the conditioning
rule for `onZero widehat_y h` is positive. -/
theorem one_sub_singleton_pos_of_mem_sherali_adams_relaxation_of_ne_one
    {P : Set (Fin n → ℝ)} {t : ℕ}
    {widehat_y : CoeffFamily n}
    (hy : widehat_y ∈ R_{t}(P))
    (h : Fin n)
    (hh_ne_one : widehat_y ({h} : Finset (Fin n)) ≠ 1) :
    0 < 1 - widehat_y ({h} : Finset (Fin n)) := by
  exact sub_pos.mpr
    (singleton_lt_one_of_mem_sherali_adams_relaxation_of_ne_one hy h hh_ne_one)

/-- Helper for Claim 1: if every inequality in a Step-2 presentation acquires, by multiplying
with `x_h`, a lifted inequality satisfied by `widehat_y`, and `widehat_y {h}` is nonnegative and
nonzero, then the conditioned vector `onOne widehat_y h` belongs to `R_{t - 1}(P)`. -/
theorem claim_1_bar_y_mem_sherali_adams_relaxation
    (P : Set (Fin n → ℝ))
    (presentation : StepInequalityPresentation P (t - 1))
    (widehat_y : CoeffFamily n)
    (h : Fin n)
    (hh_nonneg : 0 ≤ widehat_y ({h} : Finset (Fin n)))
    (hh_nonzero : widehat_y ({h} : Finset (Fin n)) ≠ 0)
    (hpositive :
      ∀ c ∈ presentation.inequalities,
        0 ≤ linearFormEval (liftOnOne c h) widehat_y) :
    onOne widehat_y h ∈ R_{t - 1}(P) := by
  exact (presentation.mem_relaxation_iff (onOne widehat_y h)).2
    (onOne_satisfiesStepInequalities presentation widehat_y h hh_nonneg hh_nonzero hpositive)

/-- Helper for Claim 1: if every inequality in a Step-2 presentation acquires, by multiplying
with `1 - x_h`, a lifted inequality satisfied by `widehat_y`, and `widehat_y {h} ≤ 1` with
`widehat_y {h} ≠ 1`, then the conditioned vector `onZero widehat_y h` belongs to
`R_{t - 1}(P)`. -/
theorem claim_1_tilde_y_mem_sherali_adams_relaxation
    (P : Set (Fin n → ℝ))
    (presentation : StepInequalityPresentation P (t - 1))
    (widehat_y : CoeffFamily n)
    (h : Fin n)
    (hh_le_one : widehat_y ({h} : Finset (Fin n)) ≤ 1)
    (hh_ne_one : widehat_y ({h} : Finset (Fin n)) ≠ 1)
    (hnegative :
      ∀ c ∈ presentation.inequalities,
        0 ≤ linearFormEval (liftOnZero c h) widehat_y) :
    onZero widehat_y h ∈ R_{t - 1}(P) := by
  exact (presentation.mem_relaxation_iff (onZero widehat_y h)).2
    (onZero_satisfiesStepInequalities presentation widehat_y h hh_le_one hh_ne_one hnegative)

/-- Helper for Claim 1: package the two conditioned-membership conclusions into a single
conjunction once the `x_h` and `1 - x_h` Step-2 lift hypotheses have both been verified. -/
theorem claim_1_bar_y_and_tilde_y_mem_sherali_adams_relaxation
    (P : Set (Fin n → ℝ))
    (presentation : StepInequalityPresentation P (t - 1))
    (widehat_y : CoeffFamily n)
    (h : Fin n)
    (hh_nonneg : 0 ≤ widehat_y ({h} : Finset (Fin n)))
    (hh_nonzero : widehat_y ({h} : Finset (Fin n)) ≠ 0)
    (hpositive :
      ∀ c ∈ presentation.inequalities,
        0 ≤ linearFormEval (liftOnOne c h) widehat_y)
    (hh_le_one : widehat_y ({h} : Finset (Fin n)) ≤ 1)
    (hh_ne_one : widehat_y ({h} : Finset (Fin n)) ≠ 1)
    (hnegative :
      ∀ c ∈ presentation.inequalities,
        0 ≤ linearFormEval (liftOnZero c h) widehat_y) :
    onOne widehat_y h ∈ R_{t - 1}(P) ∧
      onZero widehat_y h ∈ R_{t - 1}(P) := by
  constructor
  · exact
      claim_1_bar_y_mem_sherali_adams_relaxation
        P presentation widehat_y h hh_nonneg hh_nonzero hpositive
  · exact
      claim_1_tilde_y_mem_sherali_adams_relaxation
        P presentation widehat_y h hh_le_one hh_ne_one hnegative

end Claim1
