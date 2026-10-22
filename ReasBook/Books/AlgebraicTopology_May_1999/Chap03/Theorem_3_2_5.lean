/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Definition_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory FundamentalGroup Path.Homotopic.Quotient
open scoped FundamentalGroup Pointwise

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsCoveringMap

variable {p : E → B}

/-- Helper for Theorem 3.2.5: `mapOfEq` commutes with basepoint change along a path inside a
fiber of a covering map. -/
theorem mapOfEq_comp_basepoint_change (hp : IsCoveringMap p) {b : B} {e e' : p ⁻¹' {b}}
    (δ : Path e.1 e'.1) :
    (mapOfEq ⟨p, hp.continuous⟩ e'.property).comp (γ[δ]).toMonoidHom =
      (γ[((δ.map hp.continuous).cast e.property.symm e'.property.symm)]).toMonoidHom.comp
        (mapOfEq ⟨p, hp.continuous⟩ e.property) := by
  let he : p e.1 = b := e.property
  let he' : p e'.1 = b := e'.property
  let F := FundamentalGroupoid.map ⟨p, hp.continuous⟩
  let eδ : FundamentalGroupoid.mk e.1 ≅ FundamentalGroupoid.mk e'.1 :=
    (Groupoid.isoEquivHom _ _).symm ⟦δ⟧
  let eb : FundamentalGroupoid.mk (p e.1) ≅ FundamentalGroupoid.mk b :=
    eqToIso (congrArg FundamentalGroupoid.mk he)
  let eb' : FundamentalGroupoid.mk (p e'.1) ≅ FundamentalGroupoid.mk b :=
    eqToIso (congrArg FundamentalGroupoid.mk he')
  let eδb : FundamentalGroupoid.mk b ≅ FundamentalGroupoid.mk b :=
    (Groupoid.isoEquivHom _ _).symm ⟦(δ.map hp.continuous).cast he.symm he'.symm⟧
  -- Compare the two ways of transporting the projected path class back to the basepoint `b`.
  have heδb :
      eδb = eb.symm ≪≫ F.mapIso eδ ≪≫ eb' := by
    ext
    simpa [eδb, eδ, eb, eb', F, mk_map] using
      (FundamentalGroupoid.conj_eqToHom he.symm he'.symm).symm
  ext α
  -- Evaluate both monoid homomorphisms on a loop and use functoriality of conjugation.
  change eb'.conj (F.map (eδ.conj α)) = eδb.conj (eb.conj (F.map α))
  (convert congrArg eb'.conj (F.map_conj eδ α) using 1; simp [heδb])
  rfl

/-- Helper for Theorem 3.2.5: a path joining two points of the same fiber conjugates the image
subgroup of `π₁(E)` by the projected loop in the base. -/
theorem mapOfEq_range_conjugate_of_path (hp : IsCoveringMap p) {b : B}
    (e e' : p ⁻¹' {b}) (δ : Path e.1 e'.1) :
    (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
      MulAut.conj (fromPath ⟦(δ.map hp.continuous).cast e.property.symm e'.property.symm⟧) •
        (mapOfEq ⟨p, hp.continuous⟩ e.property).range := by
  let he : p e.1 = b := e.property
  let he' : p e'.1 = b := e'.property
  let g : FundamentalGroup B b := fromPath ⟦(δ.map hp.continuous).cast he.symm he'.symm⟧
  let m : FundamentalGroup E e.1 →* FundamentalGroup B b := mapOfEq ⟨p, hp.continuous⟩ he
  let m' : FundamentalGroup E e'.1 →* FundamentalGroup B b := mapOfEq ⟨p, hp.continuous⟩ he'
  let c : FundamentalGroup E e.1 →* FundamentalGroup E e'.1 := (γ[δ]).toMonoidHom
  -- Rewrite the naturality square from the previous helper into a conjugation statement.
  have hcomp :
      m'.comp c =
        (γ[((δ.map hp.continuous).cast he.symm he'.symm)]).toMonoidHom.comp m :=
    mapOfEq_comp_basepoint_change hp δ
  have hcomp' : m'.comp c = (MulAut.conj g).toMonoidHom.comp m := by
    simpa [g] using hcomp
  have hrange : (m'.comp c).range = m'.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective c (γ[δ]).surjective,
      ← MonoidHom.range_eq_map]
  calc
    m'.range = (m'.comp c).range := hrange.symm
    _ = ((MulAut.conj g).toMonoidHom.comp m).range := by rw [hcomp']
    _ = m.range.map (MulAut.conj g).toMonoidHom := MonoidHom.range_comp _ _
    _ = MulAut.conj g • m.range := by
      rfl

/-- Helper for Theorem 3.2.5: lifting a loop at `b` from a point in the fiber ends again in the
fiber over `b`. -/
theorem liftPath_endpoint_mem_fiber (hp : IsCoveringMap p) {b : B} (e : p ⁻¹' {b})
    (γ : Path b b) :
    p (hp.liftPath γ e.1 (γ.source.trans e.2.symm) 1) = b := by
  -- Project the lifted loop back to the base and evaluate at the endpoint.
  simpa using
    (congr_fun (hp.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) 1).trans γ.target

/-- Helper for Theorem 3.2.5: the endpoint of the lifted loop defines a new point of the fiber
over `b`. -/
abbrev lifted_loop_endpoint (hp : IsCoveringMap p) {b : B} (e : p ⁻¹' {b}) (γ : Path b b) :
    p ⁻¹' {b} :=
  ⟨hp.liftPath γ e.1 (γ.source.trans e.2.symm) 1, liftPath_endpoint_mem_fiber hp e γ⟩

/-- Helper for Theorem 3.2.5: the chosen lift of a loop at `b` is a path from `e` to the lifted
endpoint in the total space. -/
abbrev lifted_loop_path (hp : IsCoveringMap p) {b : B} (e : p ⁻¹' {b}) (γ : Path b b) :
    Path e.1 (lifted_loop_endpoint hp e γ).1 :=
  Path.mk (hp.liftPath γ e.1 (γ.source.trans e.2.symm))
    (hp.liftPath_zero γ e.1 (γ.source.trans e.2.symm))
    rfl

/-- Helper for Theorem 3.2.5: projecting the chosen lifted loop back to the base recovers the
original loop. -/
theorem liftPath_projection_eq_loop (hp : IsCoveringMap p) {b : B} (e : p ⁻¹' {b})
    (γ : Path b b) :
    ((lifted_loop_path hp e γ).map hp.continuous).cast e.property.symm
      (lifted_loop_endpoint hp e γ).property.symm = γ := by
  -- The lifted path was defined precisely so that its projection is `γ` pointwise.
  ext t
  simpa [lifted_loop_path] using
    congr_fun (hp.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) t

/-- Helper for Theorem 3.2.5: every concrete loop representative of a class in `π₁(B, b)` lifts
to a fiber point whose image subgroup is the corresponding conjugate. -/
theorem exists_fiberPoint_mapOfEq_range_eq_conjugate_of_loop (hp : IsCoveringMap p) {b : B}
    (e : p ⁻¹' {b}) (γ : Path b b) :
    ∃ e' : p ⁻¹' {b},
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj (fromPath ⟦γ⟧) • (mapOfEq ⟨p, hp.continuous⟩ e.property).range := by
  refine ⟨lifted_loop_endpoint hp e γ, ?_⟩
  have hconj :=
    mapOfEq_range_conjugate_of_path (hp := hp) e (lifted_loop_endpoint hp e γ)
      (lifted_loop_path hp e γ)
  -- Replace the projected lifted loop by the original loop representative `γ`.
  rwa [liftPath_projection_eq_loop (hp := hp) e γ] at hconj

/-- Theorem 3.2.5: every conjugate of the subgroup
`p_*(π₁(E, e)) ≤ π₁(B, b)` is realized as the image subgroup coming from some other point of the
fiber `p ⁻¹' {b}`. -/
-- Proof sketch: represent `g : π₁(B, b)` by a loop at `b`, lift that loop through `p` starting at
-- `e`, and let `e'` be the endpoint of the lifted loop. The lifted path gives the required
-- conjugacy relation between the two image subgroups.
theorem exists_fiberPoint_mapOfEq_range_eq_conjugate (hp : IsCoveringMap p) {b : B}
    (e : p ⁻¹' {b}) (g : FundamentalGroup B b) :
    ∃ e' : p ⁻¹' {b},
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.property).range := by
  -- Choose a loop representative of `g`, lift it from `e`, and apply the loop-level lemma.
  simpa using
    (Path.Homotopic.Quotient.ind
      (motive := fun q : Path.Homotopic.Quotient b b ↦
        ∃ e' : p ⁻¹' {b},
          (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
            MulAut.conj (fromPath q) • (mapOfEq ⟨p, hp.continuous⟩ e.property).range)
      (fun γ ↦ exists_fiberPoint_mapOfEq_range_eq_conjugate_of_loop (hp := hp) e γ)
      (FundamentalGroup.toPath g))

end IsCoveringMap
