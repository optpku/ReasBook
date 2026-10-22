/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Construction_1_5_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open FundamentalGroup

/-- The homotopy class of the standard loop with winding number `n` in `π₁(S¹, 1)`. -/
abbrev standardLoopClass (n : ℤ) : FundamentalGroup Circle 1 :=
  fromPath ⟦standardLoop n⟧

/-- Helper for Lemma 1.5.4: the Fourier character sends `0` to the circle basepoint. -/
lemma fourierChar_zero_eq_one : Real.fourierChar (0 : ℝ) = (1 : Circle) := by
  simp

/-- Helper for Lemma 1.5.4: the Fourier character sends every integer to the circle basepoint. -/
lemma fourierChar_int_eq_one (n : ℤ) : Real.fourierChar (n : ℝ) = (1 : Circle) := by
  simpa [Real.fourierChar_apply', mul_assoc] using Circle.exp_two_pi_mul_int n

/-- Helper for Lemma 1.5.4: the standard loop is the Fourier character of the lifted line
`s ↦ ns`. -/
lemma standardLoop_eq_fourierChar_mul (n : ℤ) (s : unitInterval) :
    standardLoop n s = Real.fourierChar ((n : ℝ) * (s : ℝ)) := by
  -- Rewrite the loop into the textbook exponential and simplify the scalar arithmetic.
  rw [standardLoop_apply, Real.fourierChar_apply']
  congr 1
  ring

/-- Helper for Lemma 1.5.4: the image of the straight segment from `0` to `n` under
`Real.fourierChar` is the standard loop of degree `n`. -/
lemma segment_zero_map_cast_eq_standardLoop (n : ℤ) :
    ((Path.segment (0 : ℝ) n).map Real.continuous_fourierChar).cast
      fourierChar_zero_eq_one.symm (fourierChar_int_eq_one n).symm = standardLoop n := by
  ext s
  -- Compare both paths pointwise after rewriting the segment and the standard loop formula.
  rw [standardLoop_eq_fourierChar_mul]
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
    SetLike.coe_eq_coe]
  rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
  congr 1
  ring

/-- Helper for Lemma 1.5.4: after translating the lift by an integer, the mapped segment still
represents the same standard loop. -/
lemma segment_translate_map_cast_eq_standardLoop (m n : ℤ) :
    ((Path.segment (n : ℝ) ((n + m : ℤ) : ℝ)).map Real.continuous_fourierChar).cast
      (fourierChar_int_eq_one n).symm
      (fourierChar_int_eq_one (n + m)).symm = standardLoop m := by
  ext s
  -- Rewrite the translated segment as `n + ms`, then use the additivity of `fourierChar`.
  rw [standardLoop_eq_fourierChar_mul]
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
    Int.cast_add, SetLike.coe_eq_coe]
  rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
  have hline : (1 - (s : ℝ)) * (n : ℝ) + (s : ℝ) * ((n : ℝ) + (m : ℝ)) =
      (n : ℝ) + (m : ℝ) * (s : ℝ) := by
    ring
  rw [hline]
  calc
    Real.fourierChar ((n : ℝ) + (m : ℝ) * (s : ℝ)) =
        Real.fourierChar (n : ℝ) * Real.fourierChar ((m : ℝ) * (s : ℝ)) := by
          simpa using (Real.fourierChar.map_add_eq_mul' (n : ℝ) ((m : ℝ) * (s : ℝ)))
    _ = Real.fourierChar ((m : ℝ) * (s : ℝ)) := by
          simp [fourierChar_int_eq_one]

/-- Helper for Lemma 1.5.4: concatenating the standard loops of degrees `n` and `m` is homotopic
to the standard loop of degree `m + n`. -/
lemma concat_standardLoop_homotopic_standardLoop_add (m n : ℤ) :
    ((standardLoop n).trans (standardLoop m)).Homotopic (standardLoop (m + n)) := by
  let expMap : C(ℝ, Circle) := ⟨Real.fourierChar, Real.continuous_fourierChar⟩
  let liftedConcat : Path (0 : ℝ) (((n + m : ℤ) : ℝ)) :=
    (Path.segment (0 : ℝ) n).trans (Path.segment (n : ℝ) (((n + m : ℤ) : ℝ)))
  let liftedSingle : Path (0 : ℝ) (((n + m : ℤ) : ℝ)) :=
    Path.segment (0 : ℝ) (((n + m : ℤ) : ℝ))
  -- In `ℝ`, any two paths with the same endpoints are homotopic.
  have hlifted : liftedConcat.Homotopic liftedSingle :=
    SimplyConnectedSpace.paths_homotopic liftedConcat liftedSingle
  have hstart : Real.fourierChar (0 : ℝ) = (1 : Circle) := fourierChar_zero_eq_one
  have hmid : Real.fourierChar (n : ℝ) = (1 : Circle) := fourierChar_int_eq_one n
  have hend : Real.fourierChar (((n + m : ℤ) : ℝ)) = (1 : Circle) :=
    fourierChar_int_eq_one (n + m)
  have hmapped :
      ((liftedConcat.map expMap.continuous).cast hstart.symm hend.symm).Homotopic
        ((liftedSingle.map expMap.continuous).cast hstart.symm hend.symm) := by
    -- Map the lifted homotopy down to the circle, then recast both endpoints to `1`.
    simpa [hstart, hend] using Path.Homotopic.map hlifted expMap
  have hconcat :
      ((liftedConcat.map expMap.continuous).cast hstart.symm hend.symm) =
        (standardLoop n).trans (standardLoop m) := by
    -- The concatenated lifted path maps to the two standard loops in sequence.
    dsimp [liftedConcat, expMap]
    rw [Path.map_trans, Path.cast_trans _ _ hstart.symm hmid.symm hend.symm]
    rw [segment_zero_map_cast_eq_standardLoop, segment_translate_map_cast_eq_standardLoop]
  have hsingle :
      ((liftedSingle.map expMap.continuous).cast hstart.symm hend.symm) =
        standardLoop (m + n) := by
    -- The straight lifted segment is exactly the degree-`m+n` standard loop.
    dsimp [liftedSingle, expMap]
    simpa [add_comm] using segment_zero_map_cast_eq_standardLoop (n + m)
  exact hconcat.symm ▸ hsingle.symm ▸ hmapped

/-- Lemma 1.5.4: the standard loop classes multiply by adding winding numbers, so
`[f_m] [f_n] = [f_{m+n}]` in `π₁(S¹, 1)`. -/
-- Proof sketch: compare the concatenation of `standardLoop m` and `standardLoop n`
-- with `standardLoop (m + n)` pointwise using multiplication of exponentials on `Circle`,
-- then pass to homotopy classes and transport the result into `FundamentalGroup Circle 1`.
theorem standardLoopClass_add (m n : ℤ) :
    standardLoopClass m * standardLoopClass n = standardLoopClass (m + n) := by
  -- Multiplication in `π₁` is concatenation of loop classes, with the usual order reversal.
  change FundamentalGroup.fromPath ⟦(standardLoop n).trans (standardLoop m)⟧ =
      FundamentalGroup.fromPath ⟦standardLoop (m + n)⟧
  -- The lifted real-line argument supplies the required homotopy of loops.
  exact congrArg FundamentalGroup.fromPath
    (Quotient.sound (concat_standardLoop_homotopic_standardLoop_add m n))

/-- Helper for Lemma 1.5.4: the degree-zero standard loop is the constant loop at `1`. -/
lemma standardLoop_zero_eq_refl : standardLoop 0 = Path.refl (1 : Circle) := by
  ext s
  -- The exponent vanishes identically, so the loop is constant.
  simp [standardLoop_apply]

/-- Helper for Lemma 1.5.4: the degree-zero standard loop class is the identity element. -/
lemma standardLoopClass_zero : standardLoopClass 0 = 1 := by
  -- Rewrite both sides as classes of explicit loops and simplify the zero loop.
  change FundamentalGroup.fromPath ⟦standardLoop 0⟧ =
      FundamentalGroup.fromPath ⟦Path.refl (1 : Circle)⟧
  simp [standardLoop_zero_eq_refl]

/-- Helper for Lemma 1.5.4: the standard loop classes define a homomorphism
`Multiplicative ℤ → π₁(S¹, 1)`. -/
def standardLoopClass_hom : Multiplicative ℤ →* FundamentalGroup Circle 1 :=
  { toFun := fun a ↦ standardLoopClass (Multiplicative.toAdd a)
    map_one' := standardLoopClass_zero
    map_mul' := fun a b ↦
      (standardLoopClass_add (Multiplicative.toAdd a) (Multiplicative.toAdd b)).symm }

/-- The class of the once-around loop generates the standard loop classes by integer powers. -/
-- Proof sketch: identify `(standardLoopClass 1) ^ n` with the value at `ofAdd n` of the
-- canonical `zpowersHom` out of `Multiplicative ℤ`, then compare with `standardLoopClass n`
-- using `standardLoopClass_add`.
theorem standardLoopClass_one_zpow (n : ℤ) :
    standardLoopClass 1 ^ n = standardLoopClass n := by
  -- Evaluate the homomorphism at `ofAdd n`; its value is the `n`th power of the generator.
  have happly := MonoidHom.apply_mint (α := FundamentalGroup Circle 1)
    standardLoopClass_hom (Multiplicative.ofAdd n)
  simpa [standardLoopClass_hom] using happly.symm
