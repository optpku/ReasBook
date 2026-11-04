/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_definition_4_8_1_extra_1

noncomputable section Theorem434LinearForm

variable {n : ℕ}

/-- The coefficient sum appearing in mixing inequality `(4.29)`: the coefficient of each selected
coordinate is the increment of the corresponding fractional part over the previous one, starting
from `0`. -/
def mixingInequalityTypeOneRawSumAux
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * x i.succ + mixingInequalityTypeOneRawSumAux b x fi is

/-- The floor contribution subtracted from the selected coordinates in the shifted version of
mixing inequality `(4.29)`. -/
def mixingInequalityFloorSumAux
    (b : Fin n → ℚ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * (⌊b i⌋ : ℝ) + mixingInequalityFloorSumAux b fi is

/-- The selected-coordinate sum appearing in mixing inequality `(4.29)` after subtracting the
floor part of each chosen successor coordinate. -/
def mixingInequalityTypeOneSumAux
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * (x i.succ - (⌊b i⌋ : ℝ)) + mixingInequalityTypeOneSumAux b x fi is

/-- The left-hand-side increment sum for mixing inequality `(4.29)`. -/
def mixingInequalityTypeOneSum
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : ℝ :=
  mixingInequalityTypeOneSumAux b x 0 s

/-- The accumulated floor contribution in the shifted-coordinate mixing inequalities. -/
def mixingInequalityFloorSum
    (b : Fin n → ℚ) (s : List (Fin n)) : ℝ :=
  mixingInequalityFloorSumAux b 0 s

/-- The selected-coordinate coefficient contribution in the linear form realizing mixing
inequality `(4.29)`. -/
def mixingInequalityTypeOneCoeffAux
    (b : Fin n → ℚ) : ℝ → List (Fin n) → Fin (n + 1) → ℝ
  | _, [] => fun _ ↦ 0
  | prev, i :: is =>
      fun j ↦
        (if j = i.succ then -(mixingFractionalPart b i - prev) else 0) +
          mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is j

/-- The coefficient vector whose linear inequality is exactly mixing inequality `(4.29)`. -/
def mixingInequalityTypeOneCoeff
    (b : Fin n → ℚ) (s : List (Fin n)) : Fin (n + 1) → ℝ :=
  fun j ↦ (if j = 0 then (-1 : ℝ) else 0) + mixingInequalityTypeOneCoeffAux b 0 s j

/-- The right-hand side of the linear form realizing shifted mixing inequality `(4.29)`. -/
def mixingInequalityTypeOneRhs
    (b : Fin n → ℚ) (s : List (Fin n)) : ℝ :=
  match s.reverse with
  | [] => 0
  | last :: _ => -mixingFractionalPart b last - mixingInequalityFloorSum b s

/-- The coefficient vector whose linear inequality is exactly mixing inequality `(4.30)`. -/
def mixingInequalityTypeTwoCoeff
    (b : Fin n → ℚ) (s : List (Fin n)) : Fin (n + 1) → ℝ :=
  match s, s.reverse with
  | first :: _, last :: _ =>
      fun j ↦
        mixingInequalityTypeOneCoeff b s j +
          (if j = first.succ then -(1 - mixingFractionalPart b last) else 0)
  | _, _ => mixingInequalityTypeOneCoeff b s

/-- The right-hand side of the linear form realizing shifted mixing inequality `(4.30)`. -/
def mixingInequalityTypeTwoRhs
    (b : Fin n → ℚ) (s : List (Fin n)) : ℝ :=
  match s, s.reverse with
  | first :: _, last :: _ =>
      -mixingFractionalPart b last - mixingInequalityFloorSum b s -
        (1 - mixingFractionalPart b last) * (⌊b first⌋ : ℝ)
  | _, _ => 0

end Theorem434LinearForm
