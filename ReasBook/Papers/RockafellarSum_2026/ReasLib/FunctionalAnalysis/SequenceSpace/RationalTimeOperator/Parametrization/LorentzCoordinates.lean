/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.Analysis.InnerProductSpace.HilbertProd2
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.Point
public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator

/-!
# Lorentz coordinates

This module defines the positive and negative coordinates on a parametrized
Lorentz subspace.
-/

public section

noncomputable section

namespace Lorentz

/-- A coordinate at which the nonzero vector `d` does not vanish. -/
private noncomputable def nonzeroCoordinate (d : C0Seq) (hd : d ≠ 0) : ℕ :=
  Classical.choose
    (Function.support_nonempty_iff.mpr (DFunLike.coe_injective.ne hd))

/-- The coordinate selected from a nonzero vector is nonzero. -/
private theorem nonzeroCoordinate_spec (d : C0Seq) (hd : d ≠ 0) :
    d (nonzeroCoordinate d hd) ≠ 0 := by
  -- A nonzero sequence has nonempty support, and the chosen coordinate lies in it.
  have hsupport : (Function.support (d : ℕ → ℝ)).Nonempty :=
    Function.support_nonempty_iff.mpr (DFunLike.coe_injective.ne hd)
  exact Function.mem_support.mp (Classical.choose_spec hsupport)

/-- The scalar parameter recovered intrinsically from a point of `parametrizedSubspace d`. -/
private noncomputable def parameterScalar (d : C0Seq) (hd : d ≠ 0)
    (z : parametrizedSubspace d) : ℝ :=
  (z.1.1 + L1Seq.positiveOperator z.1.2) (nonzeroCoordinate d hd) /
    d (nonzeroCoordinate d hd)

/-- The scalar value used to define the positive Lorentz coordinate. -/
private noncomputable def positiveCoordinateValue (d : C0Seq) (hd : d ≠ 0)
    (z : parametrizedSubspace d) : ℝ :=
  (parameterScalar d hd z + C0Seq.pairingL d z.1.2) / 2

/-- The positive-coordinate value is additive when the parametrization is injective. -/
private theorem positiveCoordinateValue_add (d : C0Seq) (hd : d ≠ 0)
    (z w : parametrizedSubspace d) :
    positiveCoordinateValue d hd (z + w) =
      positiveCoordinateValue d hd z + positiveCoordinateValue d hd w := by
  -- Expand the recovered parameter and use linearity of every coordinate map.
  unfold positiveCoordinateValue parameterScalar
  simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, map_add,
    ZeroAtInftyContinuousMap.add_apply]
  -- The remaining equality is the distributive law for division by fixed scalars.
  ring

/-- The positive-coordinate value is homogeneous when the parametrization is injective. -/
private theorem positiveCoordinateValue_smul (d : C0Seq) (hd : d ≠ 0)
    (r : ℝ) (z : parametrizedSubspace d) :
    positiveCoordinateValue d hd (r • z) = r • positiveCoordinateValue d hd z := by
  -- Expand the coordinate value and push scalar multiplication through the linear maps.
  unfold positiveCoordinateValue parameterScalar
  simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, map_smul,
    ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
    smul_eq_mul]
  -- Both sides now have the same scalar factor.
  ring

/-- The positive Lorentz coordinate `P` on the parametrized subspace. -/
noncomputable def positiveCoordinate (d : C0Seq) (hd : d ≠ 0) :
    parametrizedSubspace d →ₗ[ℝ] ℝ where
  toFun := positiveCoordinateValue d hd
  map_add' := positiveCoordinateValue_add d hd
  map_smul' := positiveCoordinateValue_smul d hd

/-- The positive Lorentz coordinate of the canonical point represented by `(a, t)`. -/
@[simp]
theorem positiveCoordinate_apply (d : C0Seq) (hd : d ≠ 0) (a : L1Seq) (t : ℝ) :
    positiveCoordinate d hd (parametrizedPoint d a t) =
      (t + C0Seq.pairingL d a) / 2 := by
  -- Expose the scalar formula and rewrite the canonical point through the parametrization.
  change positiveCoordinateValue d hd (parametrizedPoint d a t) = _
  unfold positiveCoordinateValue parameterScalar
  rw [parametrizedPoint_apply, parametrization_apply]
  -- The selected support coordinate permits cancellation of the recovered parameter.
  have hq : d (nonzeroCoordinate d hd) ≠ 0 := nonzeroCoordinate_spec d hd
  simp only [ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
    ZeroAtInftyContinuousMap.neg_apply, smul_eq_mul]
  field_simp [hq]
  ring

/-- The Hilbert-product value used to define the negative Lorentz coordinate. -/
private noncomputable def negativeCoordinateValue (d : C0Seq) (hd : d ≠ 0)
    (z : parametrizedSubspace d) : HilbertProd2 UnitL2 :=
  HilbertProd2.mk (L1Seq.intervalCoordinateOperator z.1.2)
    ((parameterScalar d hd z - C0Seq.pairingL d z.1.2) / 2)

/-- The negative-coordinate value is additive when the parametrization is injective. -/
private theorem negativeCoordinateValue_add (d : C0Seq) (hd : d ≠ 0)
    (z w : parametrizedSubspace d) :
    negativeCoordinateValue d hd (z + w) =
      negativeCoordinateValue d hd z + negativeCoordinateValue d hd w := by
  -- Equality in the Hilbert product is checked on its two coordinates.
  apply HilbertProd2.ext
  · unfold negativeCoordinateValue
    change L1Seq.intervalCoordinateOperator (z.1.2 + w.1.2) =
      L1Seq.intervalCoordinateOperator z.1.2 +
        L1Seq.intervalCoordinateOperator w.1.2
    exact (L1Seq.intervalCoordinateOperator).map_add z.1.2 w.1.2
  · unfold negativeCoordinateValue
    change (parameterScalar d hd (z + w) - C0Seq.pairingL d (z + w).1.2) / 2 =
      (parameterScalar d hd z - C0Seq.pairingL d z.1.2) / 2 +
        (parameterScalar d hd w - C0Seq.pairingL d w.1.2) / 2
    -- Recovering the scalar parameter commutes with addition coordinatewise.
    have hparameter : parameterScalar d hd (z + w) =
        parameterScalar d hd z + parameterScalar d hd w := by
      unfold parameterScalar
      simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add,
        ZeroAtInftyContinuousMap.add_apply, map_add]
      field_simp [nonzeroCoordinate_spec d hd]
      ring
    rw [hparameter]
    simp only [Submodule.coe_add, Prod.snd_add, map_add]
    ring

/-- The negative-coordinate value is homogeneous when the parametrization is injective. -/
private theorem negativeCoordinateValue_smul (d : C0Seq) (hd : d ≠ 0)
    (r : ℝ) (z : parametrizedSubspace d) :
    negativeCoordinateValue d hd (r • z) = r • negativeCoordinateValue d hd z := by
  -- Equality in the Hilbert product reduces homogeneity to its two components.
  apply HilbertProd2.ext
  · change L1Seq.intervalCoordinateOperator (r • z.1.2) =
      r • L1Seq.intervalCoordinateOperator z.1.2
    exact (L1Seq.intervalCoordinateOperator).map_smul r z.1.2
  · change (parameterScalar d hd (r • z) - C0Seq.pairingL d (r • z).1.2) / 2 =
      r • ((parameterScalar d hd z - C0Seq.pairingL d z.1.2) / 2)
    -- Recovering the scalar parameter commutes with real scalar multiplication.
    have hparameter : parameterScalar d hd (r • z) =
        r * parameterScalar d hd z := by
      unfold parameterScalar
      simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd,
        ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
        map_smul, smul_eq_mul]
      field_simp [nonzeroCoordinate_spec d hd]
    rw [hparameter]
    simp only [Submodule.coe_smul, Prod.smul_snd, map_smul, smul_eq_mul]
    ring

/-- The negative Lorentz coordinate `N` on the parametrized subspace. -/
noncomputable def negativeCoordinate (d : C0Seq) (hd : d ≠ 0) :
    parametrizedSubspace d →ₗ[ℝ] HilbertProd2 UnitL2 where
  toFun := negativeCoordinateValue d hd
  map_add' := negativeCoordinateValue_add d hd
  map_smul' := negativeCoordinateValue_smul d hd

/-- The negative Lorentz coordinate of the canonical point represented by `(a, t)`. -/
@[simp]
theorem negativeCoordinate_apply (d : C0Seq) (hd : d ≠ 0) (a : L1Seq) (t : ℝ) :
    negativeCoordinate d hd (parametrizedPoint d a t) =
      HilbertProd2.mk (L1Seq.intervalCoordinateOperator a)
        ((t - C0Seq.pairingL d a) / 2) := by
  -- Rewrite the canonical point, then compare the two Hilbert-product coordinates.
  change negativeCoordinateValue d hd (parametrizedPoint d a t) = _
  unfold negativeCoordinateValue parameterScalar
  rw [parametrizedPoint_apply, parametrization_apply]
  have hq : d (nonzeroCoordinate d hd) ≠ 0 := nonzeroCoordinate_spec d hd
  apply HilbertProd2.ext
  · rfl
  · change
      (((( -L1Seq.positiveOperator a + t • d) + L1Seq.positiveOperator a)
          (nonzeroCoordinate d hd) /
          d (nonzeroCoordinate d hd)) - C0Seq.pairingL d a) / 2 =
        (t - C0Seq.pairingL d a) / 2
    -- Cancel the nonzero selected coordinate to identify the recovered scalar with `t`.
    simp only [ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
      ZeroAtInftyContinuousMap.neg_apply, smul_eq_mul]
    field_simp [hq]
    ring

end Lorentz
