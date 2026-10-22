/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Definition_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open CategoryTheory FundamentalGroup Path.Homotopic.Quotient
open scoped FundamentalGroup Pointwise

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B}

private theorem fundamentalGroup_mapOfEq_comp_basepointChange (hp : IsCoveringMap p)
    {b : B} {e e' : p ⁻¹' {b}} (δ : Path e.1 e'.1) :
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
  have heδb :
      eδb = eb.symm ≪≫ F.mapIso eδ ≪≫ eb' := by
    ext
    simpa [eδb, eδ, eb, eb', F, mk_map] using
      (FundamentalGroupoid.conj_eqToHom he.symm he'.symm).symm
  ext α
  change eb'.conj (F.map (eδ.conj α)) = eδb.conj (eb.conj (F.map α))
  (convert congrArg eb'.conj (F.map_conj eδ α) using 1; simp [heδb])
  rfl

private theorem fundamentalGroup_map_range_conjugate_of_path (hp : IsCoveringMap p) {b : B}
    (e e' : p ⁻¹' {b}) (δ : Path e.1 e'.1) :
    ∃ g : FundamentalGroup B b,
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.property).range := by
  let he : p e.1 = b := e.property
  let he' : p e'.1 = b := e'.property
  let g : FundamentalGroup B b := fromPath ⟦(δ.map hp.continuous).cast he.symm he'.symm⟧
  refine ⟨g, ?_⟩
  let m : FundamentalGroup E e.1 →* FundamentalGroup B b := mapOfEq ⟨p, hp.continuous⟩ he
  let m' : FundamentalGroup E e'.1 →* FundamentalGroup B b := mapOfEq ⟨p, hp.continuous⟩ he'
  let c : FundamentalGroup E e.1 →* FundamentalGroup E e'.1 := (γ[δ]).toMonoidHom
  have hcomp :
      m'.comp c =
        (γ[((δ.map hp.continuous).cast he.symm he'.symm)]).toMonoidHom.comp m :=
    fundamentalGroup_mapOfEq_comp_basepointChange hp δ
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

/-- If two points in the fiber `p ⁻¹' {b}` are joined by a path in `E`, then the image subgroups
of the induced maps on fundamental groups at those points are conjugate inside `π₁(B, b)`. -/
-- Proof sketch: choose a path `δ` joining the two fiber points. The projected loop `(p ∘ δ)` at
-- `b` defines the conjugating element `g : π₁(B, b)`, and naturality of `mapOfEq` with respect to
-- basepoint change identifies the two image subgroups up to the inner automorphism `MulAut.conj g`.
theorem fundamentalGroup_map_range_conjugate (hp : IsCoveringMap p) {b : B}
    (e e' : p ⁻¹' {b}) (h : Joined e.1 e'.1) :
    ∃ g : FundamentalGroup B b,
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.property).range :=
  fundamentalGroup_map_range_conjugate_of_path hp e e' h.somePath

/-- Theorem 3.2.4: if `E` is path connected and `e,e' : E` lie in the same fiber of a covering
map `p : E → B`, then the image subgroups of the induced maps on fundamental groups at `e` and
`e'` are conjugate inside `π₁(B, b)`. -/
theorem fundamentalGroup_map_range_conjugate_of_pathConnectedSpace [PathConnectedSpace E]
    (hp : IsCoveringMap p) {b : B} (e e' : p ⁻¹' {b}) :
    ∃ g : FundamentalGroup B b,
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.property).range :=
  fundamentalGroup_map_range_conjugate hp e e' (PathConnectedSpace.joined e.1 e'.1)

end IsCoveringMap
