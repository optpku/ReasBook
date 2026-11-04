/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4.ch5_sec5_4_definition_5_4_extra_1

/- Lemma 10.8 rewrites the full-coordinate intersection `⋂_{j = 1}^n P_j` through the Chapter 5
owner theorem `lift_project_closure_univ_eq_iInter_coordinate_lift_project_hull`, so this file
recalls that canonical bridge instead of duplicating a parallel local theorem. -/
recall lift_project_closure_univ_eq_iInter_coordinate_lift_project_hull

section Lemma108

variable {n : ℕ}

/-- Lemma 10.8 (1). If the semidefinite relaxation `N` is contained in each coordinate
lift-and-project set `P_j`, then `N ⊆ ⋂_{j = 1}^n P_j`. -/
theorem semidefinite_relaxation_subset_iInter_coordinate_lift_project_hull
    (P N : Set (Fin n → ℝ))
    (hN : ∀ j : Fin n, N ⊆ coordinate_lift_project_hull P j) :
    N ⊆ ⋂ j : Fin n, coordinate_lift_project_hull P j := by
  exact Set.subset_iInter hN

/-- If one chosen coordinate lift-and-project set `P_j` is contained in `P`, then the full
intersection `⋂_{j = 1}^n P_j` is contained in `P`. -/
theorem iInter_coordinate_lift_project_hull_subset_of_coordinate
    (P : Set (Fin n → ℝ))
    (j : Fin n)
    (hPj : coordinate_lift_project_hull P j ⊆ P) :
    (⋂ k : Fin n, coordinate_lift_project_hull P k) ⊆ P := by
  exact Set.Subset.trans
    (Set.iInter_subset (fun k : Fin n ↦ coordinate_lift_project_hull P k) j) hPj

/-- Lemma 10.8 (2). If `n > 0` and every coordinate lift-and-project set `P_j` is contained in
`P`, then `⋂_{j = 1}^n P_j ⊆ P`. -/
theorem iInter_coordinate_lift_project_hull_subset
    (P : Set (Fin n → ℝ))
    (hn : 0 < n)
    (hP : ∀ j : Fin n, coordinate_lift_project_hull P j ⊆ P) :
    (⋂ j : Fin n, coordinate_lift_project_hull P j) ⊆ P := by
  exact iInter_coordinate_lift_project_hull_subset_of_coordinate P ⟨0, hn⟩ (hP ⟨0, hn⟩)

end Lemma108
