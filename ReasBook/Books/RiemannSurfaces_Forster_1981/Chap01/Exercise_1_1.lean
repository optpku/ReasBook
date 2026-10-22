/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Topology.Compactification.OnePoint.Sphere

open scoped OnePoint
open Metric

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `onePointEquivSphereOfFinrankEq`, `stereographic'`,
  `OnePoint.instTopologicalSpace`.
- Verified locally: `OnePoint.isOpen_iff_of_mem`, `onePointEquivSphereOfFinrankEq`,
  `EuclideanSpace.finAddEquivProd`, and the `CompactSpace`/`T2Space` instances on
  `OnePoint (EuclideanSpace ℝ (Fin n))`.
- Owner choice: model the textbook space `ℝ^n ∪ {∞}` by the canonical one-point compactification
  `OnePoint (EuclideanSpace ℝ (Fin n))`; keep compactness and Hausdorffness on that owner, and
  expose the stereographic projection itself by the textbook coordinate formula.
-/

/-- Exercise 1.1 (1): the one-point compactification `OnePoint (EuclideanSpace ℝ (Fin n))`,
i.e. the textbook space `ℝ^n ∪ {∞}` with the compact-complement topology at `∞`, is compact. In
particular this gives the stated result for `n ≥ 1`. -/
theorem onePointEuclidean_compact (n : ℕ) :
    CompactSpace (OnePoint (EuclideanSpace ℝ (Fin n))) :=
  inferInstance

/-- Exercise 1.1 (2): the one-point compactification `OnePoint (EuclideanSpace ℝ (Fin n))` of
`ℝ^n` is Hausdorff. In particular this gives the stated result for `n ≥ 1`. -/
theorem onePointEuclidean_hausdorff (n : ℕ) :
    T2Space (OnePoint (EuclideanSpace ℝ (Fin n))) :=
  inferInstance

/-- The textbook stereographic projection `S^n → ℝ^n ∪ {∞}` written on the canonical target
`OnePoint (EuclideanSpace ℝ (Fin n))`. -/
def stereographicProjection (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      OnePoint (EuclideanSpace ℝ (Fin n)) :=
  fun x ↦
    let e : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) :=
      EuclideanSpace.finAddEquivProd
    let y : EuclideanSpace ℝ (Fin n) :=
      (e x.1).1
    let t : ℝ :=
      ((e x.1).2 : EuclideanSpace ℝ (Fin 1)) 0
    if t = 1 then
      (∞ : OnePoint (EuclideanSpace ℝ (Fin n)))
    else
      (((1 : ℝ) / (1 - t)) • y : EuclideanSpace ℝ (Fin n))

/-- The defining formula for `stereographicProjection`. -/
theorem stereographicProjection_def (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    stereographicProjection n x =
      let e : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ]
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) :=
        EuclideanSpace.finAddEquivProd
      let y : EuclideanSpace ℝ (Fin n) :=
        (e x.1).1
      let t : ℝ :=
        ((e x.1).2 : EuclideanSpace ℝ (Fin 1)) 0
      if t = 1 then
        (∞ : OnePoint (EuclideanSpace ℝ (Fin n)))
      else
        (((1 : ℝ) / (1 - t)) • y : EuclideanSpace ℝ (Fin n)) := rfl

/-- The Euclidean dimension count needed to invoke the canonical one-point compactification
homeomorphism. -/
private theorem finrank_euclideanSpace_add_one_eq_card_fin_succ (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + 1 = Fintype.card (Fin (n + 1)) := by
  simp

private def canonicalOnePointEuclideanSphereHomeomorph (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₜ
      OnePoint (EuclideanSpace ℝ (Fin n)) :=
  (onePointEquivSphereOfFinrankEq (finrank_euclideanSpace_add_one_eq_card_fin_succ n)).symm

/-- Exercise 1.1 (3): the unit sphere `S^n ⊆ ℝ^{n+1}` is homeomorphic to the one-point
compactification `ℝ^n ∪ {∞}`. This bundles the textbook stereographic projection itself as a
homeomorphism, using the canonical one-point compactification homeomorphism only as a private
bridge for the inverse and continuity data. -/
def stereographicProjectionHomeomorph (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₜ
      OnePoint (EuclideanSpace ℝ (Fin n)) where
  toEquiv :=
    { toFun := stereographicProjection n
      invFun := (canonicalOnePointEuclideanSphereHomeomorph n).symm
      left_inv := by
        sorry
      right_inv := by
        sorry }
  continuous_toFun := by
    sorry
  continuous_invFun := (canonicalOnePointEuclideanSphereHomeomorph n).symm.continuous

@[simp] theorem stereographicProjectionHomeomorph_apply (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    stereographicProjectionHomeomorph n x = stereographicProjection n x :=
  rfl

/-- Exercise 1.1 (3): the textbook stereographic projection itself is a homeomorphism from `S^n`
to the one-point compactification `ℝ^n ∪ {∞}`. -/
theorem stereographicProjection_homeomorphism (n : ℕ) :
    IsHomeomorph (stereographicProjection n) := by
  simpa using (stereographicProjectionHomeomorph n).isHomeomorph
