/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Definition_1_7_1
import AlgebraicTopology_May_1999.Chap01.Lemma_1_7_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContinuousMap CircleDegree FundamentalGroup

/-- Lemma 1.7.3 (1): every constant self-map of `S¹` has degree `0`. -/
-- Proof sketch: first use path connectedness of `S¹` and mathlib's
-- `ContinuousMap.homotopic_const_iff` to homotope the constant map at `z` to the constant map at
-- `1`; then apply the chapter's canonical homotopy-invariance theorem
-- `circleDegree_eq_of_homotopic` and identify the constant map at `1` with the zeroth power of
-- `ContinuousMap.id Circle`.
theorem circleDegree_const (z : Circle) :
    deg(ContinuousMap.const Circle z) = 0 := by
  have hz : (ContinuousMap.const Circle z).Homotopic (1 : C(Circle, Circle)) := by
    rw [show (1 : C(Circle, Circle)) = ContinuousMap.const Circle (1 : Circle) by rfl]
    simpa using (ContinuousMap.homotopic_const_iff).2 (PathConnectedSpace.joined z 1)
  calc
    deg(ContinuousMap.const Circle z) = deg((1 : C(Circle, Circle))) :=
      circleDegree_eq_of_homotopic _ _ hz
    _ = 0 := by
      have hspec :=
          circleDegree_spec (1 : C(Circle, Circle)) (Path.refl (1 : Circle))
      have htrivial :
          γ[Path.refl (1 : Circle)]
              (FundamentalGroup.map (1 : C(Circle, Circle)) 1 (standardLoopClass 1)) = 1 := by
        -- Rewrite the transported generator through `mapOfEq`, then identify the mapped loop as
        -- the constant loop at the basepoint.
        change
          (FundamentalGroup.mapOfEq (1 : C(Circle, Circle)) rfl)
              (FundamentalGroup.fromPath ⟦standardLoop 1⟧) = 1
        have hmap :
            (FundamentalGroup.mapOfEq (1 : C(Circle, Circle)) rfl)
                (FundamentalGroup.fromPath ⟦standardLoop 1⟧) =
              FundamentalGroup.fromPath
                ⟦((standardLoop 1).map (1 : C(Circle, Circle)).continuous).cast
                    rfl.symm rfl.symm⟧ := by
          simpa using
            (FundamentalGroup.mapOfEq_apply
              (f := (1 : C(Circle, Circle))) (h := rfl) (p := standardLoop 1))
        rw [hmap]
        -- The constant map sends every point of the loop to the basepoint, hence produces the
        -- trivial element of `π₁(S¹, 1)`.
        change
          FundamentalGroup.fromPath
              ⟦((standardLoop 1).map (1 : C(Circle, Circle)).continuous).cast
                  rfl.symm rfl.symm⟧ = 1
        congr 1
      have hstd : standardLoopClass (deg((1 : C(Circle, Circle)))) = standardLoopClass 0 := by
        -- Compare the specification of degree with the trivial transported loop.
        rw [← hspec, standardLoopClass_zero]
        exact htrivial
      have hindex := congrArg circleFundamentalGroupLiftIndex hstd
      rw [circleFundamentalGroupLiftIndex_standardLoop,
        circleFundamentalGroupLiftIndex_standardLoop] at hindex
      exact hindex

/-- Helper for Lemma 1.7.3: the power map `z ↦ z^n` sends the standard generator of
`π₁(S¹, 1)` to `standardLoopClass n` after the endpoint is recast to the basepoint. -/
lemma id_zpow_maps_standardLoopClass (n : ℤ) :
    FundamentalGroup.mapOfEq ((ContinuousMap.id Circle : C(Circle, Circle)) ^ n) (by simp)
      (standardLoopClass 1) = standardLoopClass n := by
  let f : C(Circle, Circle) := (ContinuousMap.id Circle) ^ n
  have hbase : f 1 = (1 : Circle) := by
    simp [f]
  have hpath :
      ((standardLoop 1).map f.continuous).cast hbase.symm hbase.symm = standardLoop n := by
    -- Compute the image of the standard once-around loop pointwise under the power map.
    ext s
    rw [Path.cast_coe, Path.map_coe, Function.comp_apply, ContinuousMap.zpow_apply,
      ContinuousMap.id_apply, standardLoop_apply, standardLoop_apply]
    have h1 : 2 * Real.pi * (1 : ℤ) * (s : ℝ) = 2 * Real.pi * (s : ℝ) := by
      ring
    rw [h1]
    rw [← Circle.exp_intCast_mul (2 * Real.pi * (s : ℝ)) n]
    congr 1
    ring_nf
  have hmap := FundamentalGroup.mapOfEq_apply (f := f) (h := hbase) (p := standardLoop 1)
  calc
    (FundamentalGroup.mapOfEq f hbase) (standardLoopClass 1) =
        FundamentalGroup.fromPath
          ⟦((standardLoop 1).map f.continuous).cast hbase.symm hbase.symm⟧ := by
            -- `mapOfEq` identifies the generator image with the mapped and recast loop.
            simpa [standardLoopClass] using hmap
    _ = FundamentalGroup.fromPath ⟦standardLoop n⟧ := by
          -- The mapped loop is exactly the degree-`n` standard loop.
          rw [hpath]
    _ = standardLoopClass n := by
          rfl

/-- Helper for Lemma 1.7.3: transporting the image of the standard generator under the power map
back to the basepoint along the casted reflexive path yields `standardLoopClass n`. -/
lemma id_zpow_transported_generator (n : ℤ) :
    let f : C(Circle, Circle) := (ContinuousMap.id Circle) ^ n
    let hbase : f 1 = (1 : Circle) := by
      simp [f]
    let a : Path (f 1) (1 : Circle) := (Path.refl (1 : Circle)).cast hbase rfl
    γ[a] (FundamentalGroup.map f 1 (standardLoopClass 1)) = standardLoopClass n := by
  let f : C(Circle, Circle) := (ContinuousMap.id Circle) ^ n
  have hbase : f 1 = (1 : Circle) := by
    simp [f]
  let mapped : Path (f 1) (f 1) := (standardLoop 1).map f.continuous
  let a : Path (f 1) (1 : Circle) := (Path.refl (1 : Circle)).cast hbase rfl
  have hleft : (a.symm.trans mapped).Homotopic (mapped.cast hbase.symm rfl) := by
    -- The left comparison path is constant, so adjoining it does not change the homotopy class.
    dsimp [a, mapped]
    simpa using
      Path.Homotopic.refl_trans (((standardLoop 1).map f.continuous).cast hbase.symm rfl)
  have hright :
      ((mapped.cast hbase.symm rfl).trans a).Homotopic (mapped.cast hbase.symm hbase.symm) := by
    -- The right comparison path is also constant, so the trailing segment is homotopically
    -- trivial.
    dsimp [a, mapped]
    simpa using
      Path.Homotopic.trans_refl
        (((standardLoop 1).map f.continuous).cast hbase.symm hbase.symm)
  have hconj : ((a.symm.trans mapped).trans a).Homotopic (mapped.cast hbase.symm hbase.symm) := by
    -- Combine the two constant-path cancellations around the mapped loop.
    exact (Path.Homotopic.hcomp hleft (Path.Homotopic.refl a)).trans hright
  have hmapped :
      FundamentalGroup.fromPath ⟦mapped.cast hbase.symm hbase.symm⟧ = standardLoopClass n := by
    have hmap := FundamentalGroup.mapOfEq_apply (f := f) (h := hbase) (p := standardLoop 1)
    calc
      FundamentalGroup.fromPath ⟦mapped.cast hbase.symm hbase.symm⟧ =
          (FundamentalGroup.mapOfEq f hbase) (standardLoopClass 1) := by
            -- Re-express the recast mapped loop via `mapOfEq`.
            symm
            simpa [mapped, standardLoopClass] using hmap
      _ = standardLoopClass n := by
            -- The preceding helper computes this image explicitly.
            simpa [f] using id_zpow_maps_standardLoopClass n
  -- Rewrite transport along the chosen path into conjugation of the mapped loop.
  change γ[a] (FundamentalGroup.fromPath ⟦mapped⟧) = standardLoopClass n
  rw [fundamentalGroupMulEquivOfPath_apply_fromPath]
  have hfromPath :
      FundamentalGroup.fromPath ⟦(a.symm.trans mapped).trans a⟧ =
        FundamentalGroup.fromPath ⟦mapped.cast hbase.symm hbase.symm⟧ := by
    exact congrArg FundamentalGroup.fromPath (Quotient.sound hconj)
  calc
    FundamentalGroup.fromPath ⟦(a.symm.trans mapped).trans a⟧ =
        FundamentalGroup.fromPath ⟦mapped.cast hbase.symm hbase.symm⟧ := hfromPath
    _ = standardLoopClass n := hmapped

/-- Lemma 1.7.3 (2): the power map `x ↦ x ^ n` on `S¹`, written as the pointwise `n`-th power of
`ContinuousMap.id Circle`, has degree `n`. -/
-- Proof sketch: compute the induced map on the standard generator of `π₁(S¹, 1)` using the
-- identification of `π₁(S¹, 1)` with `ℤ`; the map `x ↦ x ^ n` sends the generator to its `n`-fold
-- power, hence corresponds to multiplication by `n`.
theorem circleDegree_id_zpow (n : ℤ) :
    deg((ContinuousMap.id Circle) ^ n) = n := by
  let f : C(Circle, Circle) := (ContinuousMap.id Circle) ^ n
  have hbase : f 1 = (1 : Circle) := by
    simp [f]
  let a : Path (f 1) (1 : Circle) := (Path.refl (1 : Circle)).cast hbase rfl
  have hspec := circleDegree_spec f a
  have hstd : standardLoopClass (deg(f)) = standardLoopClass n := by
    -- Compare the degree specification with the explicit generator computation for the power map.
    rw [← hspec]
    simpa [f, a, hbase] using id_zpow_transported_generator n
  have hindex := congrArg circleFundamentalGroupLiftIndex hstd
  rw [circleFundamentalGroupLiftIndex_standardLoop,
    circleFundamentalGroupLiftIndex_standardLoop] at hindex
  simpa [f] using hindex
