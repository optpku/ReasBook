/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1

open scoped Matrix

section Theorem514

variable {m n : ℕ}

/-- Helper for Theorem 5.14: every normalized integral row product coordinate lies in the fixed
columnwise integer interval determined by `A`. -/
lemma normalizedCutCoefficient_mem_Icc
    (A : Matrix (Fin m) (Fin n) ℤ)
    {u : Fin m → ℝ}
    (hu_nonneg : ∀ i : Fin m, 0 ≤ u i)
    (hu_lt_one : ∀ i : Fin m, u i < 1)
    {j : Fin n}
    {z : ℤ}
    (hz : (u ᵥ* (A.map (Int.castRingHom ℝ))) j = (z : ℝ)) :
    z ∈ Set.Icc (∑ i : Fin m, min (A i j) 0) (∑ i : Fin m, max (A i j) 0) := by
  -- Bound each summand between the negative and positive parts of the corresponding matrix entry.
  have hlowerR :
      ((∑ i : Fin m, min (A i j) 0 : ℤ) : ℝ) ≤
        (u ᵥ* (A.map (Int.castRingHom ℝ))) j := by
    calc
      ((∑ i : Fin m, min (A i j) 0 : ℤ) : ℝ)
          = ∑ i : Fin m, ((min (A i j) 0 : ℤ) : ℝ) := by
              simp
      _ ≤ ∑ i : Fin m, u i * (A i j : ℝ) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            by_cases hij : 0 ≤ A i j
            · have hui : 0 ≤ u i := hu_nonneg i
              have hA_nonneg : 0 ≤ (A i j : ℝ) := by exact_mod_cast hij
              simpa [min_eq_right hij] using mul_nonneg hui hA_nonneg
            · have hA_nonpos : A i j ≤ 0 := le_of_lt (lt_of_not_ge hij)
              have hui : 0 ≤ u i := hu_nonneg i
              have hmul_nonpos : u i * (A i j : ℝ) ≤ 0 := by
                have hA_nonposR : (A i j : ℝ) ≤ 0 := by exact_mod_cast hA_nonpos
                exact mul_nonpos_of_nonneg_of_nonpos hui hA_nonposR
              have hmul_lower : (A i j : ℝ) ≤ u i * (A i j : ℝ) := by
                have hui_le_one : u i ≤ 1 := (hu_lt_one i).le
                have hA_nonposR : (A i j : ℝ) ≤ 0 := by exact_mod_cast hA_nonpos
                nlinarith
              simpa [min_eq_left hA_nonpos] using hmul_lower
      _ = (u ᵥ* (A.map (Int.castRingHom ℝ))) j := by
            simp [Matrix.vecMul, dotProduct]
  have hupperR :
      (u ᵥ* (A.map (Int.castRingHom ℝ))) j ≤
        ((∑ i : Fin m, max (A i j) 0 : ℤ) : ℝ) := by
    calc
      (u ᵥ* (A.map (Int.castRingHom ℝ))) j
          = ∑ i : Fin m, u i * (A i j : ℝ) := by
              simp [Matrix.vecMul, dotProduct]
      _ ≤ ∑ i : Fin m, ((max (A i j) 0 : ℤ) : ℝ) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            by_cases hij : 0 ≤ A i j
            · have hui : 0 ≤ u i := hu_nonneg i
              have hui_le_one : u i ≤ 1 := (hu_lt_one i).le
              have hmul : u i * (A i j : ℝ) ≤ (A i j : ℝ) := by
                have hA_nonneg : 0 ≤ (A i j : ℝ) := by exact_mod_cast hij
                nlinarith
              simpa [max_eq_left hij] using hmul
            · have hA_nonpos : A i j ≤ 0 := le_of_lt (lt_of_not_ge hij)
              have hui : 0 ≤ u i := hu_nonneg i
              have hmul_nonpos : u i * (A i j : ℝ) ≤ 0 := by
                have hA_nonposR : (A i j : ℝ) ≤ 0 := by exact_mod_cast hA_nonpos
                exact mul_nonpos_of_nonneg_of_nonpos hui hA_nonposR
              simpa [max_eq_right hA_nonpos] using hmul_nonpos
      _ = ((∑ i : Fin m, max (A i j) 0 : ℤ) : ℝ) := by simp
  constructor
  · rw [hz] at hlowerR
    exact_mod_cast hlowerR
  · rw [hz] at hupperR
    exact_mod_cast hupperR

/-- Helper for Theorem 5.14: the rounded right-hand side of a normalized multiplier lies in a
fixed integer interval determined by `b`. -/
lemma normalizedCutRhs_mem_Icc
    (b : Fin m → ℤ)
    {u : Fin m → ℝ}
    (hu_nonneg : ∀ i : Fin m, 0 ≤ u i)
    (hu_lt_one : ∀ i : Fin m, u i < 1) :
    Int.floor (u ⬝ᵥ fun i ↦ (b i : ℝ)) ∈
      Set.Icc (∑ i : Fin m, min (b i) 0) (∑ i : Fin m, max (b i) 0) := by
  -- The same coordinatewise bounds apply to the scalar dot product, then `floor` stays inside the
  -- enclosing integral interval.
  have hlowerR :
      ((∑ i : Fin m, min (b i) 0 : ℤ) : ℝ) ≤ u ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
    calc
      ((∑ i : Fin m, min (b i) 0 : ℤ) : ℝ)
          = ∑ i : Fin m, ((min (b i) 0 : ℤ) : ℝ) := by
              simp
      _ ≤ ∑ i : Fin m, u i * (b i : ℝ) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            by_cases hbi : 0 ≤ b i
            · have hui : 0 ≤ u i := hu_nonneg i
              have hb_nonneg : 0 ≤ (b i : ℝ) := by exact_mod_cast hbi
              simpa [min_eq_right hbi] using mul_nonneg hui hb_nonneg
            · have hb_nonpos : b i ≤ 0 := le_of_lt (lt_of_not_ge hbi)
              have hui : 0 ≤ u i := hu_nonneg i
              have hmul_lower : (b i : ℝ) ≤ u i * (b i : ℝ) := by
                have hui_le_one : u i ≤ 1 := (hu_lt_one i).le
                have hb_nonposR : (b i : ℝ) ≤ 0 := by exact_mod_cast hb_nonpos
                nlinarith
              simpa [min_eq_left hb_nonpos] using hmul_lower
      _ = u ⬝ᵥ (fun i ↦ (b i : ℝ)) := by simp [dotProduct]
  have hupperR :
      u ⬝ᵥ (fun i ↦ (b i : ℝ)) ≤ ((∑ i : Fin m, max (b i) 0 : ℤ) : ℝ) := by
    calc
      u ⬝ᵥ (fun i ↦ (b i : ℝ)) = ∑ i : Fin m, u i * (b i : ℝ) := by simp [dotProduct]
      _ ≤ ∑ i : Fin m, ((max (b i) 0 : ℤ) : ℝ) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            by_cases hbi : 0 ≤ b i
            · have hui : 0 ≤ u i := hu_nonneg i
              have hui_le_one : u i ≤ 1 := (hu_lt_one i).le
              have hmul : u i * (b i : ℝ) ≤ (b i : ℝ) := by
                have hb_nonneg : 0 ≤ (b i : ℝ) := by exact_mod_cast hbi
                nlinarith
              simpa [max_eq_left hbi] using hmul
            · have hb_nonpos : b i ≤ 0 := le_of_lt (lt_of_not_ge hbi)
              have hui : 0 ≤ u i := hu_nonneg i
              have hmul_nonpos : u i * (b i : ℝ) ≤ 0 := by
                have hb_nonposR : (b i : ℝ) ≤ 0 := by exact_mod_cast hb_nonpos
                exact mul_nonpos_of_nonneg_of_nonpos hui hb_nonposR
              simpa [max_eq_right hb_nonpos] using hmul_nonpos
      _ = ((∑ i : Fin m, max (b i) 0 : ℤ) : ℝ) := by simp
  constructor
  · exact Int.le_floor.mpr hlowerR
  · exact_mod_cast ((Int.floor_le _).trans hupperR)

/-- Helper for Theorem 5.14: the normalized cut pairs coming from multipliers `u` with
`0 ≤ u < 1` form a finite family. -/
lemma existsFiniteNormalizedChvatalPairs
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) :
    ∃ t : ℕ, ∃ cuts : Fin t → ((Fin n → ℤ) × ℤ),
      (∀ k : Fin t,
        ∃ u : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ u i) ∧
          (∀ i : Fin m, u i < 1) ∧
          (∀ j : Fin n, (u ᵥ* (A.map (Int.castRingHom ℝ))) j = ((cuts k).1 j : ℝ)) ∧
          Int.floor (u ⬝ᵥ fun i ↦ (b i : ℝ)) = (cuts k).2) ∧
      ∀ u : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ u i) →
        (∀ i : Fin m, u i < 1) →
        (∀ j : Fin n, ∃ z : ℤ, (u ᵥ* (A.map (Int.castRingHom ℝ))) j = (z : ℝ)) →
        ∃ k : Fin t,
          (∀ j : Fin n, (u ᵥ* (A.map (Int.castRingHom ℝ))) j = ((cuts k).1 j : ℝ)) ∧
          Int.floor (u ⬝ᵥ fun i ↦ (b i : ℝ)) = (cuts k).2 := by
  classical
  let coeffLower : Fin n → ℤ := fun j ↦ ∑ i : Fin m, min (A i j) 0
  let coeffUpper : Fin n → ℤ := fun j ↦ ∑ i : Fin m, max (A i j) 0
  let rhsLower : ℤ := ∑ i : Fin m, min (b i) 0
  let rhsUpper : ℤ := ∑ i : Fin m, max (b i) 0
  let coeffBox : Set (Fin n → ℤ) :=
    {c | ∀ j : Fin n, c j ∈ Set.Icc (coeffLower j) (coeffUpper j)}
  let cutPairs : Set ((Fin n → ℤ) × ℤ) :=
    {cd |
      ∃ u : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ u i) ∧
        (∀ i : Fin m, u i < 1) ∧
        (∀ j : Fin n, (u ᵥ* (A.map (Int.castRingHom ℝ))) j = (cd.1 j : ℝ)) ∧
        Int.floor (u ⬝ᵥ fun i ↦ (b i : ℝ)) = cd.2}
  have hcoeffBoxFinite : coeffBox.Finite := by
    -- Enumerate the bounded integral coefficient vectors coordinatewise.
    simpa [coeffBox, Set.pi] using
      (Set.Finite.pi' (t := fun j : Fin n ↦ Set.Icc (coeffLower j) (coeffUpper j))
        fun j ↦ Set.finite_Icc (coeffLower j) (coeffUpper j))
  have hcutPairsFinite : cutPairs.Finite := by
    have hsubset :
        cutPairs ⊆ coeffBox ×ˢ Set.Icc rhsLower rhsUpper := by
      intro cd hcd
      rcases hcd with ⟨u, hu_nonneg, hu_lt_one, hcoeff, hrhs⟩
      refine ⟨?_, ?_⟩
      · intro j
        exact normalizedCutCoefficient_mem_Icc A hu_nonneg hu_lt_one (hcoeff j)
      · simpa [rhsLower, rhsUpper, hrhs] using normalizedCutRhs_mem_Icc b hu_nonneg hu_lt_one
    exact (hcoeffBoxFinite.prod (Set.finite_Icc rhsLower rhsUpper)).subset hsubset
  obtain ⟨t, cuts, _hcuts_inj, hcuts_range⟩ := hcutPairsFinite.fin_param
  refine ⟨t, cuts, ?_, ?_⟩
  · -- Every enumerated pair comes from a normalized multiplier by construction.
    intro k
    have hk : cuts k ∈ cutPairs := by
      rw [← hcuts_range]
      exact ⟨k, rfl⟩
    exact hk
  · -- Every normalized multiplier contributes one of the enumerated cut pairs.
    intro u hu_nonneg hu_lt_one hu_int
    let cd : (Fin n → ℤ) × ℤ :=
      (fun j ↦ Classical.choose (hu_int j), Int.floor (u ⬝ᵥ fun i ↦ (b i : ℝ)))
    have hcd : cd ∈ cutPairs := by
      refine ⟨u, hu_nonneg, hu_lt_one, ?_, rfl⟩
      intro j
      exact Classical.choose_spec (hu_int j)
    rw [← hcuts_range] at hcd
    rcases hcd with ⟨k, hk⟩
    refine ⟨k, ?_, ?_⟩
    · intro j
      simpa [cd] using congrArg Prod.fst hk ▸ Classical.choose_spec (hu_int j)
    · simpa [cd] using (congrArg Prod.snd hk).symm

/-- Helper for Theorem 5.14: subtracting the integer floor part from a Chvátal multiplier
preserves integrality of the row product. -/
lemma fractionalPartRowIntegral
    (A : Matrix (Fin m) (Fin n) ℤ)
    {u : Fin m → ℝ}
    (hu_int : ∀ j : Fin n, ∃ z : ℤ, (u ᵥ* (A.map (Int.castRingHom ℝ))) j = (z : ℝ)) :
    ∀ j : Fin n,
      ∃ z : ℤ,
        (((fun i : Fin m ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ))) j) = (z : ℝ) := by
  let uFrac : Fin m → ℝ := fun i ↦ Int.fract (u i)
  let uFloor : Fin m → ℤ := fun i ↦ Int.floor (u i)
  let uFloorR : Fin m → ℝ := fun i ↦ (uFloor i : ℝ)
  intro j
  rcases hu_int j with ⟨z, hz⟩
  let zFloor : ℤ := uFloor ⬝ᵥ fun i ↦ A i j
  have hu_decomp : u = uFrac + uFloorR := by
    funext i
    change u i = Int.fract (u i) + (Int.floor (u i) : ℝ)
    exact (Int.fract_add_floor (u i)).symm
  have hfloor_row :
      (uFloorR ᵥ* (A.map (Int.castRingHom ℝ))) j = (zFloor : ℝ) := by
    simp [uFloorR, uFloor, zFloor, Matrix.vecMul, dotProduct]
  have hsplit :
      (u ᵥ* (A.map (Int.castRingHom ℝ))) j =
        (((fun i : Fin m ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ))) j) + (zFloor : ℝ) := by
    calc
      (u ᵥ* (A.map (Int.castRingHom ℝ))) j
          = ((uFrac + uFloorR) ᵥ* (A.map (Int.castRingHom ℝ))) j := by rw [hu_decomp]
      _ = ((uFrac ᵥ* (A.map (Int.castRingHom ℝ))) j) +
            ((uFloorR ᵥ* (A.map (Int.castRingHom ℝ))) j) := by
              simpa using congrFun
                (Matrix.add_vecMul (A.map (Int.castRingHom ℝ)) uFrac uFloorR) j
      _ = (((fun i : Fin m ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ))) j) + (zFloor : ℝ) := by
            rw [hfloor_row]
  refine ⟨z - zFloor, ?_⟩
  have hfrac_eq :
      (((fun i : Fin m ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ))) j) =
        (z : ℝ) - (zFloor : ℝ) := by
    linarith [hz, hsplit]
  calc
    (((fun i : Fin m ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ))) j)
        = (z : ℝ) - (zFloor : ℝ) := hfrac_eq
    _ = ((z - zFloor : ℤ) : ℝ) := by simp

/-- Helper for Theorem 5.14: the cut produced by an arbitrary multiplier is implied by the
normalized cut coming from its fractional part together with the original system `A x ≤ b`. -/
lemma fractionalPartCut_implies_multiplierCut
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    {x : Fin n → ℝ}
    (hx_poly :
      x ∈ polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)))
    {u : Fin m → ℝ}
    (hu_nonneg : ∀ i : Fin m, 0 ≤ u i)
    (hfract :
      (((fun i : Fin m ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x) ≤
        ((⌊(fun i : Fin m ↦ Int.fract (u i)) ⬝ᵥ (fun i ↦ (b i : ℝ))⌋ : ℤ) : ℝ)) :
    (u ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x ≤
      ((⌊u ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) : ℝ) := by
  let uFrac : Fin m → ℝ := fun i ↦ Int.fract (u i)
  let uFloor : Fin m → ℤ := fun i ↦ Int.floor (u i)
  let uFloorR : Fin m → ℝ := fun i ↦ (uFloor i : ℝ)
  have hu_decomp : u = uFrac + uFloorR := by
    funext i
    change u i = Int.fract (u i) + (Int.floor (u i) : ℝ)
    exact (Int.fract_add_floor (u i)).symm
  have huFloor_nonneg : ∀ i : Fin m, 0 ≤ uFloorR i := by
    intro i
    simpa [uFloorR, uFloor] using (show (0 : ℤ) ≤ Int.floor (u i) from
      Int.floor_nonneg.mpr (hu_nonneg i))
  have hx_rows : (A.map (Int.castRingHom ℝ)) *ᵥ x ≤ fun i ↦ (b i : ℝ) :=
    mem_polyhedron_le_set_iff.mp hx_poly
  have hfloor_rhs :
      (uFloorR ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x ≤
        ((uFloor ⬝ᵥ b : ℤ) : ℝ) := by
    calc
      (uFloorR ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x
          = uFloorR ⬝ᵥ ((A.map (Int.castRingHom ℝ)) *ᵥ x) := by
              rw [Matrix.dotProduct_mulVec]
      _ ≤ uFloorR ⬝ᵥ (fun i ↦ (b i : ℝ)) :=
            dotProduct_le_dotProduct_of_nonneg_left hx_rows huFloor_nonneg
      _ = ((uFloor ⬝ᵥ b : ℤ) : ℝ) := by
            simp [uFloorR, uFloor, dotProduct]
  have hu_eval :
      (u ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x =
        (((fun i : Fin m ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x) +
          ((uFloorR ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x) := by
    calc
      (u ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x
          = ((uFrac + uFloorR) ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x := by rw [hu_decomp]
      _ = ((uFrac ᵥ* (A.map (Int.castRingHom ℝ))) +
            (uFloorR ᵥ* (A.map (Int.castRingHom ℝ)))) ⬝ᵥ x := by
              rw [Matrix.add_vecMul]
      _ = (((fun i : Fin m ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x) +
            ((uFloorR ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x) := by
              simp [uFrac]
  have hu_rhs :
      u ⬝ᵥ (fun i ↦ (b i : ℝ)) =
        (uFrac ⬝ᵥ fun i ↦ (b i : ℝ)) + ((uFloor ⬝ᵥ b : ℤ) : ℝ) := by
    calc
      u ⬝ᵥ (fun i ↦ (b i : ℝ))
          = (uFrac + uFloorR) ⬝ᵥ (fun i ↦ (b i : ℝ)) := by rw [hu_decomp]
      _ = (uFrac ⬝ᵥ fun i ↦ (b i : ℝ)) + (uFloorR ⬝ᵥ fun i ↦ (b i : ℝ)) := by
            rw [add_dotProduct]
      _ = (uFrac ⬝ᵥ fun i ↦ (b i : ℝ)) + ((uFloor ⬝ᵥ b : ℤ) : ℝ) := by
            simp [uFloorR, uFloor, dotProduct]
  -- Rewrite both sides into the fractional and floor parts, then absorb the floor contribution
  -- with feasibility in the original system.
  calc
    (u ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x
        = (((fun i : Fin m ↦ Int.fract (u i)) ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x) +
            ((uFloorR ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x) := hu_eval
    _ ≤ ((⌊uFrac ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) : ℝ) + ((uFloor ⬝ᵥ b : ℤ) : ℝ) := by
          exact add_le_add hfract hfloor_rhs
    _ = ((⌊u ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) : ℝ) := by
          calc
            (((⌊uFrac ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) : ℝ) + ((uFloor ⬝ᵥ b : ℤ) : ℝ))
                = (((⌊uFrac ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) + (uFloor ⬝ᵥ b) : ℤ) : ℝ) := by
                    simp
            _ = ((⌊(uFrac ⬝ᵥ fun i ↦ (b i : ℝ)) + (uFloor ⬝ᵥ b : ℤ)⌋ : ℤ) : ℝ) := by
                  rw [Int.floor_add_intCast]
            _ = ((⌊u ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) : ℝ) := by
                  rw [hu_rhs]

/-- Theorem 5.14 (Chvátal [73]). The pure-integer Chvátal closure of the integral system
`A x ≤ b`, expressed through the Chapter 5 pure-integer owner on the matrix polyhedron
`polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ))`, is a rational polyhedron. -/
theorem chvatalClosure_is_rational_polyhedron
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) :
    is_rational_polyhedron
      (pure_integer_chvatal_closure
        (polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)))) :=
  by
  classical
  obtain ⟨t, cuts, hcuts_source, hcuts_cover⟩ := existsFiniteNormalizedChvatalPairs A b
  let Arat : Matrix (Fin (m + t)) (Fin n) ℚ := fun r j ↦
    match finSumFinEquiv.symm r with
    | Sum.inl i => (A i j : ℚ)
    | Sum.inr k => ((cuts k).1 j : ℚ)
  let brat : Fin (m + t) → ℚ := fun r ↦
    match finSumFinEquiv.symm r with
    | Sum.inl i => b i
    | Sum.inr k => (cuts k).2
  rw [is_rational_polyhedron_iff]
  refine ⟨m + t, Arat, brat, ?_⟩
  ext x
  constructor
  · intro hx
    rw [pure_integer_chvatal_closure_eq_chvatalClosure_polyhedron_le_set
      (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ))] at hx
    rw [mem_pure_integer_chvatalClosure_iff A b x] at hx
    rw [mem_polyhedron_le_set_iff]
    intro r
    rcases hsum : finSumFinEquiv.symm r with i | k
    · -- The first block reproduces the original system `A x ≤ b`.
      simpa [Arat, brat, hsum, Matrix.mulVec, dotProduct] using hx.1 i
    · -- The second block records the finitely many normalized Chvátal cuts.
      rcases hcuts_source k with ⟨u, hu_nonneg, _hu_lt_one, hcoeff, hrhs⟩
      have hu_int :
          ∀ j : Fin n, ∃ z : ℤ, (u ᵥ* (A.map (Int.castRingHom ℝ))) j = (z : ℝ) := by
        intro j
        exact ⟨(cuts k).1 j, hcoeff j⟩
      have hcut :=
        hx.2 u hu_nonneg hu_int
      have hcutRow :
          (fun j ↦ ((cuts k).1 j : ℝ)) ⬝ᵥ x ≤ ((cuts k).2 : ℝ) := by
        calc
          (fun j ↦ ((cuts k).1 j : ℝ)) ⬝ᵥ x
              = (u ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x := by
                  congr 1
                  funext j
                  exact (hcoeff j).symm
          _ ≤ ((⌊u ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) : ℝ) := hcut
          _ = ((cuts k).2 : ℝ) := by
                exact_mod_cast hrhs
      simpa [Arat, brat, hsum, Matrix.mulVec, dotProduct] using hcutRow
  · intro hx
    rw [pure_integer_chvatal_closure_eq_chvatalClosure_polyhedron_le_set
      (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ))]
    rw [mem_pure_integer_chvatalClosure_iff A b x]
    have hxPoly :
        x ∈ polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) := by
      rw [mem_polyhedron_le_set_iff]
      intro i
      have hi := (mem_polyhedron_le_set_iff.mp hx) (Fin.castAdd t i)
      simpa [Arat, brat, Matrix.mulVec, dotProduct, finSumFinEquiv_symm_apply_castAdd] using hi
    have hxCuts :
        ∀ k : Fin t,
          (fun j ↦ ((cuts k).1 j : ℝ)) ⬝ᵥ x ≤ ((cuts k).2 : ℝ) := by
      intro k
      have hk := (mem_polyhedron_le_set_iff.mp hx) (Fin.natAdd m k)
      simpa [Arat, brat, Matrix.mulVec, dotProduct, finSumFinEquiv_symm_apply_natAdd] using hk
    refine ⟨hxPoly, ?_⟩
    intro u hu_nonneg hu_int
    let uFrac : Fin m → ℝ := fun i ↦ Int.fract (u i)
    have huFrac_nonneg : ∀ i : Fin m, 0 ≤ uFrac i := by
      intro i
      exact Int.fract_nonneg (u i)
    have huFrac_lt_one : ∀ i : Fin m, uFrac i < 1 := by
      intro i
      exact Int.fract_lt_one (u i)
    have huFrac_int :
        ∀ j : Fin n, ∃ z : ℤ, (uFrac ᵥ* (A.map (Int.castRingHom ℝ))) j = (z : ℝ) :=
      fractionalPartRowIntegral A hu_int
    obtain ⟨k, hk_coeff, hk_rhs⟩ :=
      hcuts_cover uFrac huFrac_nonneg huFrac_lt_one huFrac_int
    have hfract :
        (uFrac ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x ≤
          ((⌊uFrac ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) : ℝ) := by
      have hcoeff_fun :
          uFrac ᵥ* (A.map (Int.castRingHom ℝ)) = fun j ↦ ((cuts k).1 j : ℝ) := by
        funext j
        exact hk_coeff j
      calc
        (uFrac ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x
            = (fun j ↦ ((cuts k).1 j : ℝ)) ⬝ᵥ x := by rw [hcoeff_fun]
        _ ≤ ((cuts k).2 : ℝ) := hxCuts k
        _ = ((⌊uFrac ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) : ℝ) := by
              exact_mod_cast hk_rhs.symm
    exact fractionalPartCut_implies_multiplierCut A b hxPoly hu_nonneg hfract

/-- Theorem 5.14 in the canonical Chapter 4 matrix-polyhedron spelling. -/
theorem chvatalClosure_rational_matrix_polyhedron_is_rational_polyhedron
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) :
    is_rational_polyhedron
      (pure_integer_chvatal_closure
        (rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) (Int.cast ∘ b))) := by
  simpa [rational_matrix_polyhedron] using chvatalClosure_is_rational_polyhedron A b

end Theorem514
