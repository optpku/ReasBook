/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Example_7_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Corollary_15_31

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProductSpace Pointwise

universe u v

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
private theorem submodule_image_eq_map (L : H →L[ℝ] K) (C : Submodule ℝ H) :
    L '' (C : Set H) = ((C.map L.toLinearMap : Submodule ℝ K) : Set K) := by
  ext y
  simp

omit [CompleteSpace H] in
private theorem submodule_set_add_eq_sup (C D : Submodule ℝ H) :
    (C : Set H) + (D : Set H) = ((C ⊔ D : Submodule ℝ H) : Set H) := by
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact Submodule.mem_sup.mpr ⟨u, hu, v, hv, rfl⟩
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩

omit [CompleteSpace H] in
private theorem submodule_set_sub_eq_sup (C D : Submodule ℝ H) :
    (C : Set H) - (D : Set H) = ((C ⊔ D : Submodule ℝ H) : Set H) := by
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    simpa [sub_eq_add_neg] using
      ((Submodule.mem_sup.mpr ⟨u, hu, -v, by simpa using D.neg_mem hv, rfl⟩) :
        u + -v ∈ (C ⊔ D : Submodule ℝ H))
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, -v, by simpa using D.neg_mem hv, by abel_nf⟩

-- Proof sketch: identify `D - L '' C` and `Cᗮ - L.adjoint '' Dᗮ` with the corresponding subspace
-- sums, apply Corollary 15.31(4) in each direction, and rewrite the resulting polar cones of
-- subspaces as orthogonal complements.
/-- Corollary 15.33: for closed linear subspaces `C` and `D`, the subspace sum corresponding to
`L(C) + D` is closed if and only if the orthogonal-complement sum `Cᗮ + L^*(Dᗮ)` is closed. -/
theorem isClosed_map_sup_iff_isClosed_orthogonal_sup_adjoint_map_orthogonal
    (C : Submodule ℝ H) (D : Submodule ℝ K) (L : H →L[ℝ] K)
    (hC_closed : IsClosed (C : Set H)) (hD_closed : IsClosed (D : Set K)) :
    IsClosed (((C.map L.toLinearMap) ⊔ D : Submodule ℝ K) : Set K) ↔
      IsClosed (((Cᗮ) ⊔ (Dᗮ).map L.adjoint.toLinearMap : Submodule ℝ H) : Set H) := by
  constructor
  · intro hsum
    have hsubspace :
        (D : Set K) - L '' (C : Set H) =
          (Submodule.span ℝ ((D : Set K) - L '' (C : Set H)) : Set K) := by
      rw [submodule_image_eq_map L C, submodule_set_sub_eq_sup D (C.map L.toLinearMap)]
      simp
    have hsub_closed : IsClosed ((D : Set K) - L '' (C : Set H)) := by
      rw [submodule_image_eq_map L C, submodule_set_sub_eq_sup D (C.map L.toLinearMap)]
      simpa [sup_comm] using hsum
    have hpolar_closed :=
      Set.isClosed_add_adjoint_image_polarCone_of_closed_subspace_sub_image
        (C : Set H) (D : Set K) L
        hC_closed C.convex (Set.submodule_isCone C)
        hD_closed D.convex (Set.submodule_isCone D)
        hsubspace
        hsub_closed
    have hCpolar : Set.polarCone (C : Set H) = (Cᗮ : Set H) := by
      simpa using (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule C).2
    have hDpolar : Set.polarCone (D : Set K) = (Dᗮ : Set K) := by
      simpa using (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule D).2
    rw [hCpolar, hDpolar, submodule_image_eq_map L.adjoint Dᗮ,
      submodule_set_add_eq_sup Cᗮ ((Dᗮ).map L.adjoint.toLinearMap)] at hpolar_closed
    simpa [sup_comm] using hpolar_closed
  · intro hsum
    have hsubspace :
        (Cᗮ : Set H) - L.adjoint '' (Dᗮ : Set K) =
          (Submodule.span ℝ ((Cᗮ : Set H) - L.adjoint '' (Dᗮ : Set K)) : Set H) := by
      rw [submodule_image_eq_map L.adjoint Dᗮ,
        submodule_set_sub_eq_sup Cᗮ ((Dᗮ).map L.adjoint.toLinearMap)]
      simp
    have hsub_closed : IsClosed ((Cᗮ : Set H) - L.adjoint '' (Dᗮ : Set K)) := by
      rw [submodule_image_eq_map L.adjoint Dᗮ,
        submodule_set_sub_eq_sup Cᗮ ((Dᗮ).map L.adjoint.toLinearMap)]
      simpa [sup_comm] using hsum
    have hpolar_closed :=
      Set.isClosed_add_adjoint_image_polarCone_of_closed_subspace_sub_image
        (Dᗮ : Set K) (Cᗮ : Set H) L.adjoint
        D.isClosed_orthogonal Dᗮ.convex (Set.submodule_isCone Dᗮ)
        C.isClosed_orthogonal Cᗮ.convex (Set.submodule_isCone Cᗮ)
        hsubspace
        hsub_closed
    have hCpolar : Set.polarCone (Cᗮ : Set H) = (Cᗮᗮ : Set H) := by
      simpa using (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule Cᗮ).2
    have hDpolar : Set.polarCone (Dᗮ : Set K) = (Dᗮᗮ : Set K) := by
      simpa using (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule Dᗮ).2
    have hCclosed : Cᗮᗮ = C := by
      calc
        Cᗮᗮ = C.topologicalClosure := Submodule.orthogonal_orthogonal_eq_closure C
        _ = C := hC_closed.submodule_topologicalClosure_eq
    have hDclosed : Dᗮᗮ = D := by
      calc
        Dᗮᗮ = D.topologicalClosure := Submodule.orthogonal_orthogonal_eq_closure D
        _ = D := hD_closed.submodule_topologicalClosure_eq
    rw [hDpolar, hCpolar, hDclosed, hCclosed, ContinuousLinearMap.adjoint_adjoint,
      submodule_image_eq_map L C, submodule_set_add_eq_sup D (C.map L.toLinearMap)] at hpolar_closed
    simpa [sup_comm] using hpolar_closed
