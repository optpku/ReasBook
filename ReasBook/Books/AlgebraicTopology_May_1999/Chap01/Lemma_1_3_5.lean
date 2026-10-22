/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Lemma_1_3_2
import AlgebraicTopology_May_1999.Chap01.Lemma_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

open CategoryTheory FundamentalGroup
open scoped FundamentalGroup

/-- Helper for Lemma 1.3.5: the path obtained by inserting the comparison loop
`a.trans b.symm` before `b` is homotopic to `a`. -/
lemma trans_symm_cancel_homotopic (a b : Path x y) :
    ((a.trans b.symm).trans b).Homotopic a := by
  -- Reassociate the concatenation so that `b.symm.trans b` cancels to the constant path.
  refine (Path.Homotopic.trans_assoc a b.symm b).trans ?_
  -- Replace the middle loop by the constant path and then remove the trailing constant segment.
  refine (Path.Homotopic.hcomp (Path.Homotopic.refl a) (Path.Homotopic.symm_trans b)).trans ?_
  exact Path.Homotopic.trans_refl a

/-- Helper for Lemma 1.3.5: conjugation by a loop class fixes every element of an Abelian
fundamental group. -/
lemma groupoid_conj_eq_self_of_commutative
    [Std.Commutative ((· * ·) : FundamentalGroup X x → FundamentalGroup X x → FundamentalGroup X x)]
    (α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk x) (g : FundamentalGroup X x) :
    α.conj g = g := by
  -- Convert commutativity in `π₁(X, x)` into commutation of the corresponding endomorphisms.
  rw [Iso.conj_apply]
  have hmul :
      (FundamentalGroup.fromArrow α.hom : FundamentalGroup X x) * g =
        g * (FundamentalGroup.fromArrow α.hom : FundamentalGroup X x) :=
    Std.Commutative.comm _ _
  have hcomm :
      g ≫ α.hom = α.hom ≫ g := by
    simpa [CategoryTheory.End.mul_def] using
      hmul
  -- Once the middle terms commute, the inverse and forward path cancel.
  calc
    α.inv ≫ g ≫ α.hom = α.inv ≫ (α.hom ≫ g) := by
      rw [hcomm]
    _ = (α.inv ≫ α.hom) ≫ g := by
      rw [← Category.assoc]
    _ = g := by
      simp

/-- Helper for Lemma 1.3.5: basepoint change along a loop at `x` is the identity when
`π₁(X, x)` is Abelian. -/
lemma fundamentalGroupMulEquivOfLoop_eq_one_of_commutative
    [Std.Commutative ((· * ·) : FundamentalGroup X x → FundamentalGroup X x → FundamentalGroup X x)]
    (ℓ : Path x x) :
    γ[ℓ] = (1 : FundamentalGroup X x ≃* FundamentalGroup X x) := by
  let α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk x :=
    (Groupoid.isoEquivHom _ _).symm ⟦ℓ⟧
  -- Unfold the loop action to conjugation by the corresponding groupoid isomorphism.
  ext g
  change α.conj g = g
  exact groupoid_conj_eq_self_of_commutative α g

/-- Lemma 1.3.5: if the fundamental group `π₁(X, x)` is Abelian, then the basepoint-change
isomorphism `γ[a] : π₁(X, x) → π₁(X, y)` is independent of the chosen path class from `x` to
`y`. -/
-- Proof sketch: compare `a` and `b` through the loop `a.trans b.symm` at `x`, use
-- `fundamentalGroupMulEquivOfPath_homotopic_eq` and `fundamentalGroupMulEquivOfPath_trans` to
-- write `γ[a]` as the composite of `γ[b]` with the loop-induced automorphism, and then use
-- commutativity of the canonical multiplication on `FundamentalGroup X x` to show that
-- conjugation automorphism is the identity.
theorem fundamentalGroupMulEquivOfPath_eq_of_abelian
    [Std.Commutative ((· * ·) : FundamentalGroup X x → FundamentalGroup X x → FundamentalGroup X x)]
    (a b : Path x y) :
    γ[a] = γ[b] := by
  let loop := a.trans b.symm
  have hloop : γ[loop] = (1 : FundamentalGroup X x ≃* FundamentalGroup X x) :=
    fundamentalGroupMulEquivOfLoop_eq_one_of_commutative loop
  have hpath : (loop.trans b).Homotopic a :=
    trans_symm_cancel_homotopic a b
  -- Compare `a` with `b` through the loop `a.trans b.symm` based at `x`.
  calc
    γ[a] = γ[loop.trans b] := by
      simpa [loop] using (fundamentalGroupMulEquivOfPath_homotopic_eq hpath).symm
    -- Split basepoint change along the composite into the loop action followed by `γ[b]`.
    _ = (γ[loop]).trans (γ[b]) :=
      fundamentalGroupMulEquivOfPath_trans loop b
    -- The loop action is trivial in an Abelian fundamental group.
    _ = γ[b] := by
      rw [hloop]
      ext g
      rfl
