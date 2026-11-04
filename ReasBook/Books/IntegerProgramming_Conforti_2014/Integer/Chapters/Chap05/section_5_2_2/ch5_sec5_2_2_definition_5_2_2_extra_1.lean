/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_theorem_4_51
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_1.ch5_sec5_2_1_lemma_5_13

open scoped IntegerVectorNotation Matrix

section Definition522Extra1

variable {n : ℕ}

/-- The pure-integer points of a set `P ⊆ ℝ^n`. -/
def pure_integer_points (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  P ∩ ℤ^n

/-- Membership in `pure_integer_points P` means lying in `P` and belonging to `ℤ^n`. -/
theorem mem_pure_integer_points_iff
    {P : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ pure_integer_points P ↔ x ∈ P ∧ x ∈ ℤ^n :=
  Iff.rfl

/-- Membership in `pure_integer_points P` is equivalently feasibility in `P` together with
integrality of every coordinate. -/
theorem mem_pure_integer_points_iff_forall
    {P : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ pure_integer_points P ↔ x ∈ P ∧ ∀ i, ∃ z : ℤ, x i = (z : ℝ) := by
  rw [mem_pure_integer_points_iff, mem_integerVectors_iff_forall]
  simp [Set.mem_range, eq_comm]

/-- The pure-integer hull `P_I`, represented as the convex hull of the pure-integer points of
`P`. -/
def pure_integer_hull (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  convexHull ℝ (pure_integer_points P)

/-- The pure-integer hull is the convex hull of `P ∩ ℤ^n`. -/
theorem pure_integer_hull_eq_convexHull
    (P : Set (Fin n → ℝ)) :
    pure_integer_hull P = convexHull ℝ (P ∩ ℤ^n) :=
  rfl

/-- The pure-integer Chapter 5 Chvátal closure of `P` is the set of points of `P` satisfying
every rounded valid inequality with integer coefficients. This is the source-facing set-level
owner; on a matrix presentation it agrees with the canonical Chapter 5 matrix owner
`chvatalClosure A b Finset.univ`. -/
def pure_integer_chvatal_closure (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ |
    x ∈ P ∧
      ∀ c : Fin n → ℤ, ∀ d : ℝ,
        is_valid_inequality P (fun i ↦ (c i : ℝ)) d →
          (fun i ↦ (c i : ℝ)) ⬝ᵥ x ≤ ((Int.floor d : ℤ) : ℝ)}

/-- Membership in `pure_integer_chvatal_closure P` means lying in `P` and satisfying every
rounded valid inequality with integer coefficients. -/
theorem mem_pure_integer_chvatal_closure_iff
    {P : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ pure_integer_chvatal_closure P ↔
      x ∈ P ∧
        ∀ c : Fin n → ℤ, ∀ d : ℝ,
          is_valid_inequality P (fun i ↦ (c i : ℝ)) d →
            (fun i ↦ (c i : ℝ)) ⬝ᵥ x ≤ ((Int.floor d : ℤ) : ℝ) :=
  Iff.rfl

/-- On a matrix polyhedron `polyhedron_le_set A b`, the source-facing set-level pure-integer
closure agrees with the canonical Chapter 5 matrix owner specialized to `Finset.univ`. -/
theorem pure_integer_chvatal_closure_eq_chvatalClosure_polyhedron_le_set
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    pure_integer_chvatal_closure (polyhedron_le_set A b) =
      chvatalClosure A b Finset.univ := by
  ext x
  constructor
  · intro hx
    rw [mem_pure_integer_chvatal_closure_iff] at hx
    rw [mem_chvatalClosure_iff]
    refine ⟨hx.1, ?_⟩
    intro u hu
    have hu' := (isChvatalMultiplier_univ_iff A u).1 hu
    have hvalid : is_valid_inequality (polyhedron_le_set A b) (u ᵥ* A) (u ⬝ᵥ b) := by
      intro y hy
      calc
        (u ᵥ* A) ⬝ᵥ y = u ⬝ᵥ (A *ᵥ y) := by rw [Matrix.dotProduct_mulVec]
        _ ≤ u ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hy hu'.1
    let c : Fin n → ℤ := fun j ↦ Classical.choose (hu'.2 j)
    have hc_eq : (fun j ↦ (c j : ℝ)) = u ᵥ* A := by
      funext j
      exact (Classical.choose_spec (hu'.2 j)).symm
    have hvalid' :
        is_valid_inequality (polyhedron_le_set A b) (fun j ↦ (c j : ℝ)) (u ⬝ᵥ b) := by
      simpa [hc_eq] using hvalid
    have hcut := hx.2 c (u ⬝ᵥ b) hvalid'
    simpa [hc_eq] using hcut
  · intro hx
    rw [mem_chvatalClosure_iff] at hx
    rw [mem_pure_integer_chvatal_closure_iff]
    refine ⟨hx.1, ?_⟩
    intro c d hvalid
    obtain ⟨u, hu_nonneg, hu_row, hu_le⟩ :=
      (valid_inequality_iff_exists_nonneg_row_multiplier_raw
        A b (fun j ↦ (c j : ℝ)) d ⟨x, hx.1⟩).1 hvalid
    have hu : IsChvatalMultiplier A Finset.univ u := by
      rw [isChvatalMultiplier_univ_iff]
      refine ⟨hu_nonneg, ?_⟩
      intro j
      refine ⟨c j, ?_⟩
      simpa using congrFun hu_row j
    have hfloor_int : Int.floor (u ⬝ᵥ b) ≤ Int.floor d :=
      Int.floor_mono hu_le
    have hfloor :
        (((Int.floor (u ⬝ᵥ b) : ℤ) : ℝ)) ≤ (((Int.floor d : ℤ) : ℝ)) := by
      exact_mod_cast hfloor_int
    calc
      (fun j ↦ (c j : ℝ)) ⬝ᵥ x = (u ᵥ* A) ⬝ᵥ x := by rw [← hu_row]
      _ ≤ ((Int.floor (u ⬝ᵥ b) : ℤ) : ℝ) := hx.2 u hu
      _ ≤ ((Int.floor d : ℤ) : ℝ) := hfloor

/-- Membership in the source-facing pure-integer closure of `polyhedron_le_set A b` is
equivalently membership in the canonical matrix Chvátal closure `chvatalClosure A b Finset.univ`.
-/
theorem mem_pure_integer_chvatal_closure_polyhedron_le_set_iff
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ pure_integer_chvatal_closure (polyhedron_le_set A b) ↔
      x ∈ chvatalClosure A b Finset.univ := by
  simp [pure_integer_chvatal_closure_eq_chvatalClosure_polyhedron_le_set A b]

/-- On the canonical Chapter 4 owner `rational_matrix_polyhedron A b`, the source-facing
pure-integer closure agrees with the canonical Chapter 5 matrix owner specialized to
`Finset.univ`. -/
theorem pure_integer_chvatal_closure_eq_chvatalClosure_rational_matrix_polyhedron
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    pure_integer_chvatal_closure (rational_matrix_polyhedron A b) =
      chvatalClosure (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) Finset.univ := by
  simpa [rational_matrix_polyhedron] using
    pure_integer_chvatal_closure_eq_chvatalClosure_polyhedron_le_set
      (A.map (Rat.castHom ℝ))
      (fun i ↦ (b i : ℝ))

/-- Membership in the source-facing pure-integer closure of `rational_matrix_polyhedron A b` is
equivalently membership in the canonical matrix Chvátal closure of the same rational system. -/
theorem mem_pure_integer_chvatal_closure_rational_matrix_polyhedron_iff
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : Fin n → ℝ) :
    x ∈ pure_integer_chvatal_closure (rational_matrix_polyhedron A b) ↔
      x ∈ chvatalClosure (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) Finset.univ := by
  simp [pure_integer_chvatal_closure_eq_chvatalClosure_rational_matrix_polyhedron A b]

/- Definition 5.2.2-extra-1 (1): the `t`th Chvátal closure of `P` is represented by the canonical
function iterate `(closure^[t]) P`. -/
#check (Nat.iterate :
  (Set (Fin n → ℝ) → Set (Fin n → ℝ)) → ℕ → Set (Fin n → ℝ) → Set (Fin n → ℝ))

/-- The generic iterate-rank owner underlying the Chapter 5 Chvátal rank of an inequality. It
records that `α x ≤ β` is valid for the pure-integer hull of `P`, that it is valid on the `t`th
iterate of `P`, and that no smaller iterate already satisfies it. -/
class is_iterate_rank_of_inequality
    (closure : Set (Fin n → ℝ) → Set (Fin n → ℝ))
    (P : Set (Fin n → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ)
    (t : ℕ) : Prop where
  /-- The inequality is valid for the pure-integer hull `P_I`. -/
  valid_on_integer_hull : is_valid_inequality (pure_integer_hull P) α β
  /-- The inequality is valid for the `t`th Chvátal closure of `P`. -/
  valid_on_iterate : is_valid_inequality (closure^[t] P) α β
  /-- No smaller Chvátal iterate of `P` already satisfies the inequality. -/
  minimal :
    ∀ ⦃j : ℕ⦄, j < t → ¬ is_valid_inequality (closure^[j] P) α β

/-- Proofs of `is_iterate_rank_of_inequality closure P α β t` are subsingletons because this is a
proposition. -/
instance is_iterate_rank_of_inequality_subsingleton
    (closure : Set (Fin n → ℝ) → Set (Fin n → ℝ))
    (P : Set (Fin n → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ)
    (t : ℕ) :
    Subsingleton (is_iterate_rank_of_inequality closure P α β t) :=
  inferInstance

/-- `is_iterate_rank_of_inequality` unfolds to validity on `P_I`, validity on the `t`th iterate,
and minimality of `t`. -/
theorem is_iterate_rank_of_inequality_iff
    {closure : Set (Fin n → ℝ) → Set (Fin n → ℝ)}
    {P : Set (Fin n → ℝ)}
    {α : Fin n → ℝ}
    {β : ℝ}
    {t : ℕ} :
    is_iterate_rank_of_inequality closure P α β t ↔
      is_valid_inequality (pure_integer_hull P) α β ∧
        is_valid_inequality (closure^[t] P) α β ∧
          ∀ ⦃j : ℕ⦄, j < t → ¬ is_valid_inequality (closure^[j] P) α β := by
  constructor
  · intro ht
    exact ⟨ht.valid_on_integer_hull, ht.valid_on_iterate, ht.minimal⟩
  · rintro ⟨hinteger, hvalid, hminimal⟩
    exact ⟨hinteger, hvalid, hminimal⟩

/-- If `t` is the iterate rank of `α x ≤ β`, then the inequality is not valid on any earlier
Chvátal iterate of `P`. -/
theorem is_iterate_rank_of_inequality.not_valid_on_iterate
    {closure : Set (Fin n → ℝ) → Set (Fin n → ℝ)}
    {P : Set (Fin n → ℝ)}
    {α : Fin n → ℝ}
    {β : ℝ}
    {t j : ℕ}
    (ht : is_iterate_rank_of_inequality closure P α β t)
    (hj : j < t) :
    ¬ is_valid_inequality (closure^[j] P) α β :=
  ht.minimal hj

/-- The generic iterate-rank owner underlying Chapter 5 polyhedral rank statements. It records
that the `t`th iterate of `P` reaches the pure-integer hull and that no smaller iterate does. -/
class is_iterate_rank_of_polyhedron
    (closure : Set (Fin n → ℝ) → Set (Fin n → ℝ))
    (P : Set (Fin n → ℝ))
    (t : ℕ) : Prop where
  /-- The `t`th Chvátal closure of `P` is the pure-integer hull of `P`. -/
  eq_integer_hull :
    (closure^[t] P) = pure_integer_hull P
  /-- No smaller Chvátal iterate of `P` is already the integer hull. -/
  minimal :
    ∀ ⦃j : ℕ⦄, j < t → (closure^[j] P) ≠ pure_integer_hull P

/-- Proofs of `is_iterate_rank_of_polyhedron closure P t` are subsingletons because this is a
proposition. -/
instance is_iterate_rank_of_polyhedron_subsingleton
    (closure : Set (Fin n → ℝ) → Set (Fin n → ℝ))
    (P : Set (Fin n → ℝ))
    (t : ℕ) :
    Subsingleton (is_iterate_rank_of_polyhedron closure P t) :=
  inferInstance

/-- `is_iterate_rank_of_polyhedron` unfolds to attainment of the integer hull at the `t`th
iterate together with minimality of `t`. -/
theorem is_iterate_rank_of_polyhedron_iff
    {closure : Set (Fin n → ℝ) → Set (Fin n → ℝ)}
    {P : Set (Fin n → ℝ)}
    {t : ℕ} :
    is_iterate_rank_of_polyhedron closure P t ↔
      (closure^[t] P) = pure_integer_hull P ∧
        ∀ ⦃j : ℕ⦄, j < t → (closure^[j] P) ≠ pure_integer_hull P := by
  constructor
  · intro ht
    exact ⟨ht.eq_integer_hull, ht.minimal⟩
  · rintro ⟨heq, hminimal⟩
    exact ⟨heq, hminimal⟩

/-- If `t` is the iterate rank of `P`, then no earlier iterate already equals `P_I`. -/
theorem is_iterate_rank_of_polyhedron.not_eq_integer_hull
    {closure : Set (Fin n → ℝ) → Set (Fin n → ℝ)}
    {P : Set (Fin n → ℝ)}
    {t j : ℕ}
    (ht : is_iterate_rank_of_polyhedron closure P t)
    (hj : j < t) :
    (closure^[j] P) ≠ pure_integer_hull P :=
  ht.minimal hj

end Definition522Extra1
