/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_2.ch4_sec4_8_2_lemma_4_35

section Definition130

variable {n p : ℕ}

/-- A relaxation set `P'` is a perfect formulation for a mixed-integer set `S` when it has the
same mixed-integer points and the same attained maxima for every mixed linear objective. -/
structure IsPerfectFormulation
    (S P' : Set (MixedRealPoint n p)) : Prop where
  mixedIntegerSet_eq : S = mixed_integer_points P'
  isGreatest_iff :
    ∀ (c : Fin n → ℝ) (h : Fin p → ℝ) (z : ℝ),
      IsGreatest (mixed_linear_objective c h '' S) z ↔
        IsGreatest (mixed_linear_objective c h '' P') z

/-- Build `IsPerfectFormulation S P'` from its two defining clauses. -/
def IsPerfectFormulation.ofIff
    (S P' : Set (MixedRealPoint n p))
    (hMixedIntegerSet : S = mixed_integer_points P')
    (hIsGreatest :
      ∀ (c : Fin n → ℝ) (h : Fin p → ℝ) (z : ℝ),
        IsGreatest (mixed_linear_objective c h '' S) z ↔
          IsGreatest (mixed_linear_objective c h '' P') z) :
    IsPerfectFormulation S P' :=
  { mixedIntegerSet_eq := hMixedIntegerSet
    isGreatest_iff := hIsGreatest }

/-- Expand `IsPerfectFormulation S P'` into equality of mixed-integer points together with the
all-objective `IsGreatest` equivalence. -/
theorem isPerfectFormulation_iff
    (S P' : Set (MixedRealPoint n p)) :
    IsPerfectFormulation S P' ↔
      S = mixed_integer_points P' ∧
        ∀ (c : Fin n → ℝ) (h : Fin p → ℝ) (z : ℝ),
          IsGreatest (mixed_linear_objective c h '' S) z ↔
            IsGreatest (mixed_linear_objective c h '' P') z := by
  constructor
  · intro hPerfect
    -- Read the equality and objective clauses directly from the perfect-formulation witness.
    exact ⟨hPerfect.mixedIntegerSet_eq, hPerfect.isGreatest_iff⟩
  · rintro ⟨hMixedIntegerSet, hObjectives⟩
    -- Reassemble the two defining clauses into the bundled proposition.
    exact IsPerfectFormulation.ofIff S P' hMixedIntegerSet hObjectives

variable {m' : ℕ}

/-- remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_definition_1_30.lean
Definition 1.30. A rational system `A' x + G' y ≤ b'` is a perfect formulation for `S` when
its nonnegative rational mixed-polyhedron relaxation is a perfect formulation of `S`. -/
def isPerfectFormulationOfRationalSystem
    (S : Set (MixedRealPoint n p))
    (A' : Matrix (Fin m') (Fin n) ℚ)
    (G' : Matrix (Fin m') (Fin p) ℚ)
    (b' : Fin m' → ℚ) : Prop :=
  IsPerfectFormulation S (nonnegative_rational_mixed_polyhedron A' G' b')

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_definition_1_30.lean:
the mixed-integer points of the nonnegative rational relaxation are its canonical rational
mixed-integer linear set. -/
lemma mixed_integer_points_nonnegative_rational_mixed_polyhedron_eq_rationalMixedIntegerLinearSet
    (A' : Matrix (Fin m') (Fin n) ℚ)
    (G' : Matrix (Fin m') (Fin p) ℚ)
    (b' : Fin m' → ℚ) :
    mixed_integer_points (nonnegative_rational_mixed_polyhedron A' G' b') =
      rationalMixedIntegerLinearSet A' G' b' := by
  ext xy
  constructor
  · intro hxy
    rcases (mem_mixed_integer_points_iff.mp hxy) with ⟨hPoly, hInteger⟩
    rcases hPoly with ⟨hInequalities, hx, hy⟩
    refine mem_rationalMixedIntegerLinearSet_iff.mpr ⟨hInequalities, hx, hy, ?_⟩
    have hxInteger :=
      mem_integerVectors_iff_forall.mp (mem_mixed_integer_lattice_iff.mp hInteger)
    intro j
    rcases hxInteger j with ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · intro hxy
    rcases (mem_rationalMixedIntegerLinearSet_iff.mp hxy) with
      ⟨hInequalities, hx, hy, hInteger⟩
    refine mem_mixed_integer_points_iff.mpr ⟨⟨hInequalities, hx, hy⟩, ?_⟩
    rw [mem_mixed_integer_lattice_iff, mem_integerVectors_iff_forall]
    intro j
    rcases hInteger j with ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

/-- Unfold `isPerfectFormulationOfRationalSystem S A' G' b'` into the textbook mixed-integer-set
equality and the all-objective optimal-value equivalence. -/
theorem isPerfectFormulationOfRationalSystem_iff
    (S : Set (MixedRealPoint n p))
    (A' : Matrix (Fin m') (Fin n) ℚ)
    (G' : Matrix (Fin m') (Fin p) ℚ)
    (b' : Fin m' → ℚ) :
    isPerfectFormulationOfRationalSystem S A' G' b' ↔
      S = rationalMixedIntegerLinearSet A' G' b' ∧
        ∀ (c : Fin n → ℝ) (h : Fin p → ℝ) (z : ℝ),
          IsGreatest (mixed_linear_objective c h '' S) z ↔
          IsGreatest
              (mixed_linear_objective c h '' (nonnegative_rational_mixed_polyhedron A' G' b'))
              z := by
  constructor
  · intro hPerfect
    refine ⟨hPerfect.mixedIntegerSet_eq.trans ?_, hPerfect.isGreatest_iff⟩
    exact
      mixed_integer_points_nonnegative_rational_mixed_polyhedron_eq_rationalMixedIntegerLinearSet
        A' G' b'
  · rintro ⟨hMixedIntegerSet, hObjectives⟩
    refine IsPerfectFormulation.ofIff S
      (nonnegative_rational_mixed_polyhedron A' G' b') ?_ hObjectives
    exact hMixedIntegerSet.trans
      (mixed_integer_points_nonnegative_rational_mixed_polyhedron_eq_rationalMixedIntegerLinearSet
        A' G' b').symm

#print axioms isPerfectFormulationOfRationalSystem

end Definition130
