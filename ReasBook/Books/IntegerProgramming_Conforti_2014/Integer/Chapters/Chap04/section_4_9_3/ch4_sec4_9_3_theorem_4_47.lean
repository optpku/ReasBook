/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_13.ch3_sec3_13_theorem_3_39
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_13.ch3_sec3_13_theorem_3_38
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_theorem_4_30.Decomposition
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9_3.ch4_sec4_9_3_definition_4_9_3_extra_1
import Mathlib.Analysis.Convex.KreinMilman

open scoped BigOperators Matrix Pointwise

-- The Chapter 4.9.3 mixed-integer representability owner is imported from
-- `ch4_sec4_9_3_definition_4_9_3_extra_1`; this file adds only the rational-polytope/intcone
-- surface needed for Theorem 4.47.

namespace Set

/-- A subset of `ℝ^n` is a rational polytope if it admits a finite rational vertex presentation. -/
def IsRationalPolytope {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ k : ℕ,
    ∃ v : Fin k → Fin n → ℚ,
      P = convexHull ℝ (Set.range fun i : Fin k ↦ fun j : Fin n ↦ (v i j : ℝ))

/-- A rational polytope is, in particular, a polytope for the canonical Chapter 3 owner
`Set.IsPolytope ℝ`. -/
theorem IsRationalPolytope.isPolytope
    {n : ℕ} {P : Set (Fin n → ℝ)} (hP : P.IsRationalPolytope) :
    P.IsPolytope ℝ := by
  rcases hP with ⟨k, v, rfl⟩
  exact ⟨Set.range (fun i : Fin k ↦ fun j : Fin n ↦ (v i j : ℝ)), Set.finite_range _, rfl⟩

end Set

/-- Helper for Theorem 4.47: the unit box is the convex hull of its `0/1` vertices, hence a
rational polytope. -/
private lemma unitBox_isRationalPolytope
    (n : ℕ) :
    (Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)).IsRationalPolytope := by
  let e : Fin (Fintype.card (Fin n → Bool)) ≃ (Fin n → Bool) :=
    (Fintype.equivFin (Fin n → Bool)).symm
  let v :
      Fin (Fintype.card (Fin n → Bool)) → Fin n → ℚ := fun i j ↦
        if e i j then 1 else 0
  have hRange :
      Set.range (fun i : Fin (Fintype.card (Fin n → Bool)) ↦ fun j : Fin n ↦ ((v i j : ℚ) : ℝ)) =
        zero_one_cube n := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [mem_zero_one_cube_iff]
      intro j
      by_cases hij : e i j
      · right
        simp [v, hij]
      · left
        simp [v, hij]
    · intro hx
      rw [mem_zero_one_cube_iff] at hx
      let b : Fin n → Bool := fun j ↦ x j = 1
      refine ⟨e.symm b, ?_⟩
      ext j
      have hj := hx j
      by_cases hb : b j
      · have hxj : x j = 1 := by
          simpa [b] using hb
        simp [v, e, b, hb, hxj]
      · have hxj : x j = 0 := by
          rcases hj with h0 | h1
          · exact h0
          · exfalso
            exact hb (by simpa [b, h1])
        simp [v, e, b, hb, hxj]
  have hCompact :
      IsCompact (Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)) := by
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hConvex :
      Convex ℝ (Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)) := by
    exact convex_pi fun _ _ ↦ convex_Icc (0 : ℝ) 1
  have hExtremeFinite :
      ((Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ).Finite := by
    rw [extremePoints_unit_box_eq_zero_one_cube, ← hRange]
    exact Set.finite_range _
  refine ⟨Fintype.card (Fin n → Bool), v, ?_⟩
  calc
    Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)
        = closure (convexHull ℝ ((Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ)) := by
            simpa using (closure_convexHull_extremePoints hCompact hConvex).symm
    _ = convexHull ℝ ((Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ) := by
          rw [(hExtremeFinite.isClosed_convexHull ℝ).closure_eq]
    _ = convexHull ℝ (zero_one_cube n) := by
          rw [extremePoints_unit_box_eq_zero_one_cube]
    _ = convexHull ℝ
          (Set.range (fun i : Fin (Fintype.card (Fin n → Bool)) ↦ fun j : Fin n ↦ ((v i j : ℚ) : ℝ))) := by
            rw [← hRange]

/-- Helper for Theorem 4.47: applying a rational linear map to a rational polytope preserves a
rational vertex presentation. -/
private lemma isRationalPolytope_image_rationalMatrixMulVec
    {m n : ℕ}
    {P : Set (Fin m → ℝ)}
    (hP : P.IsRationalPolytope)
    (A : Matrix (Fin n) (Fin m) ℚ) :
    ((fun x : Fin m → ℝ ↦ (A.map (Rat.castHom ℝ)) *ᵥ x) '' P).IsRationalPolytope := by
  rcases hP with ⟨k, v, hv⟩
  let w : Fin k → Fin n → ℚ := fun i ↦ A *ᵥ v i
  have hlin : IsLinearMap ℝ (fun x : Fin m → ℝ ↦ (A.map (Rat.castHom ℝ)) *ᵥ x) := by
    refine ⟨?_, ?_⟩
    · intro x y
      ext i
      simp [Matrix.mulVec_add]
    · intro a x
      ext i
      simp [Matrix.mulVec_smul]
  refine ⟨k, w, ?_⟩
  rw [hv, hlin.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    ext j
    simp [w, Matrix.mulVec, dotProduct]
  · rintro ⟨i, rfl⟩
    refine ⟨fun j : Fin m ↦ (v i j : ℝ), ⟨i, rfl⟩, ?_⟩
    ext j
    simp [w, Matrix.mulVec, dotProduct]

/-- Helper for Theorem 4.47: Minkowski sums of rational polytopes stay rational. -/
private lemma isRationalPolytope_add
    {n : ℕ}
    {P Q : Set (Fin n → ℝ)}
    (hP : P.IsRationalPolytope)
    (hQ : Q.IsRationalPolytope) :
    (P + Q).IsRationalPolytope := by
  rcases hP with ⟨k, v, hv⟩
  rcases hQ with ⟨l, w, hw⟩
  let e : Fin (Fintype.card (Fin k × Fin l)) ≃ Fin k × Fin l :=
    (Fintype.equivFin (Fin k × Fin l)).symm
  refine ⟨Fintype.card (Fin k × Fin l), fun a i ↦ v (e a).1 i + w (e a).2 i, ?_⟩
  rw [hv, hw, ← convexHull_add]
  congr 1
  ext x
  constructor
  · rintro ⟨u, ⟨i, rfl⟩, z, ⟨j, rfl⟩, rfl⟩
    refine ⟨e.symm (i, j), ?_⟩
    ext s
    simp [e]
  · rintro ⟨a, rfl⟩
    exact
      Set.mem_add.2
        ⟨fun i : Fin n ↦ (v (e a).1 i : ℝ), ⟨(e a).1, rfl⟩,
          fun i : Fin n ↦ (w (e a).2 i : ℝ), ⟨(e a).2, rfl⟩, by
            ext s
            simp [e]⟩

/-- Helper for Theorem 4.47: every rational polytope in `ℝ^n` admits a rational matrix
presentation. -/
lemma rationalPolytope_eq_rationalMatrixPolyhedron
    {n : ℕ} {P : Set (Fin n → ℝ)} (hP : P.IsRationalPolytope) :
    ∃ m : ℕ,
      ∃ A : Matrix (Fin m) (Fin n) ℚ,
        ∃ b : Fin m → ℚ,
          P = rational_matrix_polyhedron A b := by
  rcases hP with ⟨k, v, rfl⟩
  let verticesReal : Fin k → Fin n → ℝ := fun i j ↦ (v i j : ℝ)
  let rays0 : Fin 0 → Fin n → ℚ := Fin.elim0
  let L : ℕ := ∑ j : Fin k, EncodingSize.rationalVector (v j)
  have hVertices :
      ∀ j : Fin k, EncodingSize.rationalVector (v j) ≤ L := by
    intro j
    -- Bound each listed vertex encoding by the total encoding budget.
    dsimp [L]
    exact Finset.single_le_sum
      (fun j' _ ↦ Nat.zero_le (EncodingSize.rationalVector (v j')))
      (Finset.mem_univ j)
  rcases exists_rational_matrix_polyhedron_of_bounded_rational_vrepresentation_encoding
      v
      rays0
      L
      hVertices
      (by intro j; exact Fin.elim0 j) with
    ⟨π, m, A, b, hrepr, -, -⟩
  refine ⟨m, A, b, ?_⟩
  have hConeEmpty :
      cone (Set.range fun i : Fin 0 ↦ fun j : Fin n ↦ (rays0 i j : ℝ)) =
        ({0} : Set (Fin n → ℝ)) := by
    -- The empty ray family generates only the zero vector.
    simpa using (cone_empty : cone (∅ : Set (Fin n → ℝ)) = ({0} : Set (Fin n → ℝ)))
  have hAddZero :
      convexHull ℝ (Set.range verticesReal) + ({0} : Set (Fin n → ℝ)) =
        convexHull ℝ (Set.range verticesReal) := by
    -- Adding the zero singleton does not change the convex hull.
    ext x
    constructor
    · intro hx
      rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, hsum⟩
      have hzZero : z = 0 := Set.mem_singleton_iff.mp hz
      have hyEq : y = x := by
        simpa [hzZero] using hsum
      simpa [hyEq] using hy
    · intro hx
      exact Set.mem_add.mpr ⟨x, hx, 0, Set.mem_singleton 0, by simp⟩
  calc
    convexHull ℝ (Set.range verticesReal)
        = convexHull ℝ (Set.range verticesReal) +
            ({0} : Set (Fin n → ℝ)) := by
              symm
              exact hAddZero
    _ = convexHull ℝ (Set.range verticesReal) +
          cone (Set.range fun i : Fin 0 ↦ fun j : Fin n ↦ (rays0 i j : ℝ)) := by
            rw [hConeEmpty]
    _ = rational_matrix_polyhedron A b := hrepr

/-- Helper for Theorem 4.47: a finite family of rational polytopes admits simultaneous rational
matrix descriptions. -/
lemma exists_rationalMatrixPolyhedronDescriptions
    {n k : ℕ}
    {P : Fin k → Set (Fin n → ℝ)}
    (hP : ∀ i : Fin k, (P i).IsRationalPolytope) :
    ∃ m : Fin k → ℕ,
      ∃ A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ,
        ∃ b : ∀ i : Fin (k), Fin (m i) → ℚ,
          ∀ i : Fin k, P i = rational_matrix_polyhedron (A i) (b i) := by
  classical
  -- Choose one rational H-description for each rational polytope piece independently.
  choose m A b hAb using fun i : Fin k ↦ rationalPolytope_eq_rationalMatrixPolyhedron (hP i)
  exact ⟨m, A, b, hAb⟩

/-- The integer cone generated by finitely many integral directions in `ℤ^n`, viewed inside
`ℝ^n`. -/
def integral_intcone {n t : ℕ} (r : Fin t → Fin n → ℤ) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ |
    ∃ a : Fin t → ℕ,
      x = ∑ j : Fin t, (a j : ℝ) • (fun i : Fin n ↦ (r j i : ℝ))}

/-- Membership in `integral_intcone r` means admitting a nonnegative integer combination of the
generating integral directions `r`. -/
theorem mem_integral_intcone_iff
    {n t : ℕ} {r : Fin t → Fin n → ℤ} {x : Fin n → ℝ} :
    x ∈ integral_intcone r ↔
      ∃ a : Fin t → ℕ,
        x = ∑ j : Fin t, (a j : ℝ) • (fun i : Fin n ↦ (r j i : ℝ)) := by
  -- This is exactly the defining existential witness for `integral_intcone`.
  rfl

/-- Helper for Theorem 4.47: a nonempty rational polytope has trivial homogeneous matrix cone. -/
lemma homogeneousMatrixPolyhedron_eq_singleton_zero_of_rationalPolytope
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {b : Fin m → ℚ}
    (hP : (rational_matrix_polyhedron A b).IsRationalPolytope)
    (hP_nonempty : (rational_matrix_polyhedron A b).Nonempty) :
    rational_matrix_polyhedron A 0 = ({0} : Set (Fin n → ℝ)) := by
  let P : Set (Fin n → ℝ) := rational_matrix_polyhedron A b
  have hP_bounded : Bornology.IsBounded P := by
    -- Rational polytopes are bounded via the Chapter 3 polytope owner.
    rcases (Set.IsRationalPolytope.isPolytope hP) with ⟨V, hV, hVeq⟩
    simpa [P, hVeq] using (isBounded_convexHull).2 hV.isBounded
  obtain ⟨x₀, hx₀⟩ := hP_nonempty
  have htranslate :
      ({x₀} + recessionCone P) ⊆ P := by
    -- Translating a feasible point by a recession direction keeps the point feasible.
    rintro y ⟨x', hx', r, hr, rfl⟩
    rw [Set.mem_singleton_iff] at hx'
    subst x'
    rw [mem_recessionCone_iff] at hr
    simpa [P] using hr hx₀ 1 zero_le_one
  have hrec_zero : recessionCone P = ({0} : Set (Fin n → ℝ)) := by
    have hrec_bounded : Bornology.IsBounded (recessionCone P) := by
      -- The translated recession cone sits inside the bounded polytope `P`.
      obtain ⟨R, _, hP_ball⟩ := hP_bounded.subset_ball_lt 0 (0 : Fin n → ℝ)
      exact Bornology.IsBounded.subset
        (show Bornology.IsBounded (Metric.ball (0 : Fin n → ℝ) (R + ‖x₀‖)) from
          Metric.isBounded_ball)
        (by
          intro r hr
          have hxrP : x₀ + r ∈ P := by
            exact htranslate ⟨x₀, Set.mem_singleton x₀, r, hr, by simp⟩
          have hxr_ball : ‖x₀ + r‖ < R := by
            simpa [Metric.mem_ball, dist_eq_norm] using hP_ball hxrP
          have hr_eq : r = (x₀ + r) + (-x₀) := by
            ext i
            simp
          have hr_norm_le : ‖r‖ ≤ ‖x₀ + r‖ + ‖x₀‖ := by
            rw [hr_eq]
            simpa using norm_add_le (x₀ + r) (-x₀)
          have hr_norm_lt : ‖r‖ < R + ‖x₀‖ := by
            linarith
          simpa [Metric.mem_ball, dist_eq_norm] using hr_norm_lt)
    ext r
    constructor
    · intro hr
      by_cases hr0 : r = 0
      · simp [hr0]
      · obtain ⟨R, hR⟩ := hrec_bounded.subset_closedBall (0 : Fin n → ℝ)
        have hzero_mem : (0 : Fin n → ℝ) ∈ recessionCone P := zero_mem_recessionCone
        have hR_nonneg : 0 ≤ R := by
          have hzero_ball : (0 : Fin n → ℝ) ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR hzero_mem
          simpa [Metric.mem_closedBall] using hzero_ball
        have hr_norm_pos : 0 < ‖r‖ := norm_pos_iff.mpr hr0
        have hr_norm_ne : ‖r‖ ≠ 0 := ne_of_gt hr_norm_pos
        have ht_nonneg : 0 ≤ R / ‖r‖ + 1 := by positivity
        have htr_mem : ((R / ‖r‖ + 1) • r) ∈ recessionCone P :=
          smul_mem_recessionCone hr ht_nonneg
        have hmem_ball :
            ((R / ‖r‖ + 1) • r) ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR htr_mem
        have htr_bound : ‖(R / ‖r‖ + 1) • r‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hmem_ball
        have htr_norm : ‖(R / ‖r‖ + 1) • r‖ = R + ‖r‖ := by
          calc
            ‖(R / ‖r‖ + 1) • r‖ = |R / ‖r‖ + 1| * ‖r‖ := norm_smul _ _
            _ = (R / ‖r‖ + 1) * ‖r‖ := by rw [abs_of_nonneg ht_nonneg]
            _ = (R / ‖r‖) * ‖r‖ + ‖r‖ := by rw [add_mul, one_mul]
            _ = R + ‖r‖ := by rw [div_mul_cancel₀ _ hr_norm_ne]
        have hlarge : R + ‖r‖ ≤ R := by
          simpa [htr_norm] using htr_bound
        linarith
    · intro hr
      have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
      subst hr0
      exact zero_mem_recessionCone
  ext r
  constructor
  · intro hr
    have hr_nonpos : (A.map (Rat.castHom ℝ)) *ᵥ r ≤ 0 := by
      simpa using (mem_rational_matrix_polyhedron A 0 r).1 hr
    have hr_rec : r ∈ recessionCone P := by
      -- The homogeneous inequalities are exactly the recession-direction inequalities.
      rw [mem_recessionCone_iff]
      intro x hx a ha
      rw [show P = rational_matrix_polyhedron A b by rfl] at hx ⊢
      rw [mem_rational_matrix_polyhedron] at hx ⊢
      intro i
      have hmul : a * ((A.map (Rat.castHom ℝ)) *ᵥ r) i ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha (hr_nonpos i)
      have hsum :
          ((A.map (Rat.castHom ℝ)) *ᵥ x) i +
              a * ((A.map (Rat.castHom ℝ)) *ᵥ r) i ≤
            (b i : ℝ) := by
        linarith [hx i, hmul]
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
        mul_comm, mul_left_comm, mul_assoc] using hsum
    have hr_zero : r ∈ ({0} : Set (Fin n → ℝ)) := by
      simpa [hrec_zero] using hr_rec
    simpa using hr_zero
  · rintro rfl
    -- The zero vector satisfies every homogeneous inequality.
    rw [mem_rational_matrix_polyhedron]
    intro i
    simp

/-- Helper for Theorem 4.47: if every integral-cone generator vanishes, then the cone is exactly
`{0}`. -/
lemma integral_intcone_eq_singleton_zero_of_generators_eq_zero
    {n t : ℕ}
    {r : Fin t → Fin n → ℤ}
    (hr : ∀ j, (fun i : Fin n ↦ (r j i : ℝ)) = 0) :
    integral_intcone r = ({0} : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_singleton_iff]
    rcases (mem_integral_intcone_iff).1 hx with ⟨a, rfl⟩
    -- Once every generator is zero, every integer-cone combination collapses to the zero vector.
    simp [hr]
  · rintro rfl
    -- The zero vector is the empty nonnegative combination of the generators.
    exact (mem_integral_intcone_iff).2 ⟨0, by simp⟩

/-- Helper for Theorem 4.47: a nonnegative integral selector with total sum `1` has a unique
active coordinate. -/
lemma oneHotIntegralSelector
    {k : ℕ}
    (δ : Fin k → ℤ)
    (hδ_nonneg : ∀ i : Fin k, 0 ≤ δ i)
    (hδ_sum : ∑ i : Fin k, δ i = 1) :
    ∃! j : Fin k, δ j = 1 := by
  have hδ_le_one : ∀ i : Fin k, δ i ≤ 1 := by
    intro i
    let rest : ℤ := Finset.sum (Finset.univ.erase i) fun j : Fin k ↦ δ j
    have hrest_nonneg : 0 ≤ rest := by
      unfold rest
      exact Finset.sum_nonneg fun j _ ↦ hδ_nonneg j
    have hsplit : rest + δ i = 1 := by
      unfold rest
      have :
          Finset.sum (Finset.univ.erase i) (fun j : Fin k ↦ δ j) + δ i =
            ∑ j : Fin k, δ j := by
        simpa [add_comm] using
          (Finset.sum_erase_add _ _ (Finset.mem_univ i))
      rw [hδ_sum] at this
      simpa using this
    omega
  have hex : ∃ j : Fin k, δ j = 1 := by
    have h_exists_ne_zero : ∃ j : Fin k, δ j ≠ 0 := by
      by_contra hnone
      push Not at hnone
      have hsum_zero : ∑ i : Fin k, δ i = 0 := by
        simp [hnone]
      omega
    rcases h_exists_ne_zero with ⟨j, hj_ne_zero⟩
    refine ⟨j, ?_⟩
    have hzero_or_one : δ j = 0 ∨ δ j = 1 := by
      have hj_nonneg : 0 ≤ δ j := hδ_nonneg j
      have hj_le_one : δ j ≤ 1 := hδ_le_one j
      omega
    rcases hzero_or_one with hzero | hone
    · exact False.elim (hj_ne_zero hzero)
    · exact hone
  rcases hex with ⟨j, hj⟩
  refine ⟨j, hj, ?_⟩
  intro i hi
  by_contra hij
  let rest : ℤ := Finset.sum (Finset.univ.erase j) fun l : Fin k ↦ δ l
  have hsplit : rest + δ j = ∑ l : Fin k, δ l := by
    unfold rest
    simpa [add_comm] using
      (Finset.sum_erase_add _ _ (Finset.mem_univ j))
  have hrest_zero : rest = 0 := by
    rw [hδ_sum] at hsplit
    rw [hj] at hsplit
    omega
  have hi_le_rest : δ i ≤ rest := by
    unfold rest
    refine Finset.single_le_sum ?_ ?_
    · intro l _
      exact hδ_nonneg l
    · simp [hij]
  have hi_zero : δ i = 0 := by
    rw [hrest_zero] at hi_le_rest
    have hi_nonneg : 0 ≤ δ i := hδ_nonneg i
    omega
  have : False := by
    omega
  exact False.elim this

/-- Helper for Theorem 4.47: a natural selector whose total mass is `1` is one-hot. -/
lemma oneHotNatSelector
    {k : ℕ}
    (δ : Fin k → ℕ)
    (hδ_sum : ∑ i : Fin k, δ i = 1) :
    ∃! j : Fin k, δ j = 1 := by
  -- Cast the natural selector into `ℤ` so the integer one-hot lemma applies unchanged.
  have hδ_nonneg : ∀ i : Fin k, (0 : ℤ) ≤ (δ i : ℤ) := by
    intro i
    exact Int.natCast_nonneg (δ i)
  have hδ_sum_int : ∑ i : Fin k, ((δ i : ℤ)) = 1 := by
    exact_mod_cast hδ_sum
  rcases oneHotIntegralSelector (fun i ↦ (δ i : ℤ)) hδ_nonneg hδ_sum_int with
    ⟨j, hj, huniq⟩
  refine ⟨j, ?_, ?_⟩
  · exact_mod_cast hj
  · intro i hi
    apply huniq
    exact_mod_cast hi

/-- Helper for Theorem 4.47: removing empty pieces from a finite rational-polytope family does
not change its union, and the remaining family is pointwise nonempty. -/
lemma exists_reindexedNonemptyRationalPolytopeFamily
    {n k : ℕ}
    (P : Fin k → Set (Fin n → ℝ))
    (hP : ∀ i : Fin k, (P i).IsRationalPolytope) :
    ∃ k' : ℕ,
      ∃ P' : Fin k' → Set (Fin n → ℝ),
        (∀ i : Fin k', (P' i).IsRationalPolytope) ∧
        (∀ i : Fin k', (P' i).Nonempty) ∧
        (⋃ i : Fin k, P i) = ⋃ i : Fin k', P' i := by
  classical
  let I := {i : Fin k // (P i).Nonempty}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let P' : Fin (Fintype.card I) → Set (Fin n → ℝ) := fun j ↦ P ((e.symm j).1)
  refine ⟨Fintype.card I, P', ?_, ?_, ?_⟩
  · intro j
    -- Each reindexed piece comes from one of the original rational polytope pieces.
    exact hP ((e.symm j).1)
  · intro j
    -- The subtype index records nonemptiness for the retained piece.
    exact (e.symm j).2
  · -- Compare both unions by transporting witnesses through the finite reindexing equivalence.
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      let ii : I := ⟨i, ⟨x, hxi⟩⟩
      refine Set.mem_iUnion.2 ⟨e ii, ?_⟩
      simpa [P', ii]
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨j, hxj⟩
      refine Set.mem_iUnion.2 ⟨(e.symm j).1, ?_⟩
      simpa [P'] using hxj

/-- Helper for Theorem 4.47: after choosing nonempty rational matrix presentations, the textbook
selector equations with a one-hot natural selector are equivalent to membership in the union of
polytope pieces plus the common integral cone. -/
lemma mem_iUnion_rational_matrix_polyhedron_add_integral_intcone_iff_exists_oneHotLift
    {n k t : ℕ}
    {m : Fin k → ℕ}
    {A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ}
    {b : ∀ i : Fin k, Fin (m i) → ℚ}
    {r : Fin t → Fin n → ℤ}
    (hPoly : ∀ i : Fin k, (rational_matrix_polyhedron (A i) (b i)).IsRationalPolytope)
    (hNonempty : ∀ i : Fin k, (rational_matrix_polyhedron (A i) (b i)).Nonempty)
    {x : Fin n → ℝ} :
    x ∈ (⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)) + integral_intcone r ↔
      ∃ xParts : Fin k → Fin n → ℝ,
        ∃ δ : Fin k → ℕ,
          ∃ μ : Fin t → ℕ,
            (∀ i : Fin k,
              (A i).map (Rat.castHom ℝ) *ᵥ xParts i ≤
                (δ i : ℝ) • (fun j : Fin (m i) ↦ (b i j : ℝ))) ∧
            x =
              (∑ i : Fin k, xParts i) +
                ∑ j : Fin t, (μ j : ℝ) • (fun l : Fin n ↦ (r j l : ℝ)) ∧
            ∑ i : Fin k, δ i = 1 := by
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rcases Set.mem_iUnion.1 hu with ⟨i, hiu⟩
    rcases (mem_integral_intcone_iff).1 hv with ⟨a, rfl⟩
    let xParts : Fin k → Fin n → ℝ := fun j ↦ if h : j = i then u else 0
    let δ : Fin k → ℕ := fun j ↦ if j = i then 1 else 0
    refine ⟨xParts, δ, a, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst j
        -- The active block is exactly the selected point of the chosen rational polytope.
        simpa [xParts, δ, mem_rational_matrix_polyhedron] using
          (mem_rational_matrix_polyhedron (A i) (b i) u).1 hiu
      · -- Every inactive block is the zero vector and therefore satisfies the homogeneous system.
        simp [xParts, δ, hj]
    · -- The one-hot block choice makes the lifted sum collapse back to the chosen point `u`.
      have hxParts_sum : ∑ j : Fin k, xParts j = u := by
        classical
        ext l
        rw [Finset.sum_apply, Finset.sum_eq_single i]
        · simp [xParts]
        · intro j _ hj
          simp [xParts, hj]
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      simp [hxParts_sum]
    · -- The selector family is the characteristic function of the chosen index.
      simp [δ]
  · rintro ⟨xParts, δ, μ, hineq, hx, hδ_sum⟩
    rcases oneHotNatSelector δ hδ_sum with ⟨i, hδi, hδ_unique⟩
    have hδ_zero_of_ne : ∀ j : Fin k, j ≠ i → δ j = 0 := by
      intro j hj
      have hj_le_total : δ j ≤ ∑ l : Fin k, δ l := by
        refine Finset.single_le_sum ?_ ?_
        · intro l _
          exact Nat.zero_le (δ l)
        · exact Finset.mem_univ j
      have hj_le_one : δ j ≤ 1 := by
        simpa [hδ_sum] using hj_le_total
      have hj_ne_one : δ j ≠ 1 := by
        intro hδj
        exact hj (hδ_unique j hδj)
      omega
    have hxParts_zero_of_inactive : ∀ j : Fin k, j ≠ i → xParts j = 0 := by
      intro j hj
      have hδj_zero : δ j = 0 := hδ_zero_of_ne j hj
      have hxParts_mem_zero :
          xParts j ∈ rational_matrix_polyhedron (A j) 0 := by
        rw [mem_rational_matrix_polyhedron]
        simpa [hδj_zero] using hineq j
      have hzero_poly :
          rational_matrix_polyhedron (A j) 0 = ({0} : Set (Fin n → ℝ)) :=
        homogeneousMatrixPolyhedron_eq_singleton_zero_of_rationalPolytope
          (hPoly j) (hNonempty j)
      have hxParts_zero_mem : xParts j ∈ ({0} : Set (Fin n → ℝ)) := by
        simpa [hzero_poly] using hxParts_mem_zero
      simpa using hxParts_zero_mem
    have hxParts_sum :
        ∑ j : Fin k, xParts j = xParts i := by
      classical
      ext l
      rw [Fintype.sum_eq_single i]
      · intro j hj
        simp [hxParts_zero_of_inactive j hj]
    have hxPart_mem :
        xParts i ∈ rational_matrix_polyhedron (A i) (b i) := by
      rw [mem_rational_matrix_polyhedron]
      simpa [hδi] using hineq i
    have hcone_mem :
        ∑ j : Fin t, (μ j : ℝ) • (fun l : Fin n ↦ (r j l : ℝ)) ∈ integral_intcone r :=
      (mem_integral_intcone_iff).2 ⟨μ, rfl⟩
    refine Set.mem_add.2 ⟨xParts i, Set.mem_iUnion.2 ⟨i, hxPart_mem⟩,
      ∑ j : Fin t, (μ j : ℝ) • (fun l : Fin n ↦ (r j l : ℝ)), hcone_mem, ?_⟩
    -- The inactive blocks vanish, so the lifted decomposition reduces to the active polytope point.
    rw [hxParts_sum] at hx
    exact hx.symm

/-- Helper for Theorem 4.47: the selector lift stores the `k` polytope-part vectors in one
auxiliary real block indexed by `Fin k × Fin n`. -/
noncomputable def selectorConeRealAuxDim (k n : ℕ) : ℕ :=
  Fintype.card (Fin k × Fin n)

/-- Helper for Theorem 4.47: flatten a family `xParts : Fin k → Fin n → ℝ` into the single
auxiliary real block used by the mixed selector lift. -/
noncomputable def flattenSelectorParts
    {n k : ℕ} (xParts : Fin k → Fin n → ℝ) :
    Fin (selectorConeRealAuxDim k n) → ℝ :=
  fun a ↦
    let ij : Fin k × Fin n := (Fintype.equivFin (Fin k × Fin n)).symm a
    xParts ij.1 ij.2

/-- Helper for Theorem 4.47: unflatten the auxiliary real block of the mixed selector lift back
into the family of polytope-part vectors. -/
noncomputable def unflattenSelectorParts
    {n k : ℕ} (y : Fin (selectorConeRealAuxDim k n) → ℝ) :
    Fin k → Fin n → ℝ :=
  fun i j ↦ y (Fintype.equivFin (Fin k × Fin n) (i, j))

/-- Helper for Theorem 4.47: unflattening the flattened part block recovers the original family of
polytope-part vectors. -/
theorem unflattenSelectorParts_flattenSelectorParts
    {n k : ℕ} (xParts : Fin k → Fin n → ℝ) :
    unflattenSelectorParts (flattenSelectorParts xParts) = xParts := by
  -- The finite equivalence between `Fin (card (Fin k × Fin n))` and `Fin k × Fin n` records the
  -- same coordinates in both directions.
  funext i j
  simp [unflattenSelectorParts, flattenSelectorParts]

/-- Helper for Theorem 4.47: flattening the unflattened auxiliary real block returns the original
coordinate function. -/
theorem flattenSelectorParts_unflattenSelectorParts
    {n k : ℕ} (y : Fin (selectorConeRealAuxDim k n) → ℝ) :
    flattenSelectorParts (unflattenSelectorParts y) = y := by
  -- The same coordinate equivalence reconstructs the original flattened auxiliary block.
  funext a
  simp [unflattenSelectorParts, flattenSelectorParts]

/-- Helper for Theorem 4.47: decode one flattened auxiliary selector coordinate into its
underlying `(polytope part, visible coordinate)` pair. -/
private noncomputable def selectorConeFlatIndex
    {n k : ℕ} :
    Fin (selectorConeRealAuxDim k n) → Fin k × Fin n :=
  (Fintype.equivFin (Fin k × Fin n)).symm

/-- Helper for Theorem 4.47: the selector-lift rational system uses component rows, two
reconstruction row families, two selector-sum rows, and nonnegativity rows for `δ` and `μ`. -/
private inductive SelectorConeLiftRow
    {n k t : ℕ} (m : Fin k → ℕ) : Type
  | component : (i : Fin k) → Fin (m i) → SelectorConeLiftRow m
  | xEqLe : Fin n → SelectorConeLiftRow m
  | xEqGe : Fin n → SelectorConeLiftRow m
  | selectorSumLe : SelectorConeLiftRow m
  | selectorSumGe : SelectorConeLiftRow m
  | deltaNonneg : Fin k → SelectorConeLiftRow m
  | muNonneg : Fin t → SelectorConeLiftRow m
deriving Fintype, DecidableEq

/-- Helper for Theorem 4.47: the selector-lift integer block contains the selector coefficients
for the component rows, the cone coefficients for the reconstruction rows, and the pure
nonnegativity/selector-sum rows. -/
private def selectorConeLiftIntCoeff
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ) :
    SelectorConeLiftRow (n := n) (t := t) m → Fin (k + t) → ℚ
  | .component i s =>
      Fin.addCases (fun i' ↦ if i' = i then -(b i s) else 0) (fun _ ↦ 0)
  | .xEqLe l =>
      Fin.addCases (fun _ ↦ 0) (fun j ↦ -(r j l : ℚ))
  | .xEqGe l =>
      Fin.addCases (fun _ ↦ 0) (fun j ↦ (r j l : ℚ))
  | .selectorSumLe =>
      Fin.addCases (fun _ ↦ 1) (fun _ ↦ 0)
  | .selectorSumGe =>
      Fin.addCases (fun _ ↦ -1) (fun _ ↦ 0)
  | .deltaNonneg i =>
      Fin.addCases (fun i' ↦ if i' = i then -1 else 0) (fun _ ↦ 0)
  | .muNonneg j =>
      Fin.addCases (fun _ ↦ 0) (fun j' ↦ if j' = j then -1 else 0)

/-- Helper for Theorem 4.47: the selector-lift real block stores the visible `x`-variables and
the flattened family of auxiliary polytope-part vectors `xParts`. -/
private noncomputable def selectorConeLiftRealCoeff
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ) :
    SelectorConeLiftRow (n := n) (t := t) m →
      Fin (n + selectorConeRealAuxDim k n) → ℚ
  | .component i s =>
      Fin.addCases (fun _ ↦ 0) fun a ↦
        if (selectorConeFlatIndex a).1 = i then
          A i s (selectorConeFlatIndex a).2
        else
          0
  | .xEqLe l =>
      Fin.addCases
        (fun l' ↦ if l' = l then 1 else 0)
        (fun a ↦ if (selectorConeFlatIndex a).2 = l then -1 else 0)
  | .xEqGe l =>
      Fin.addCases
        (fun l' ↦ if l' = l then -1 else 0)
        (fun a ↦ if (selectorConeFlatIndex a).2 = l then 1 else 0)
  | .selectorSumLe =>
      Fin.addCases (fun _ ↦ 0) (fun _ ↦ 0)
  | .selectorSumGe =>
      Fin.addCases (fun _ ↦ 0) (fun _ ↦ 0)
  | .deltaNonneg _ =>
      Fin.addCases (fun _ ↦ 0) (fun _ ↦ 0)
  | .muNonneg _ =>
      Fin.addCases (fun _ ↦ 0) (fun _ ↦ 0)

/-- Helper for Theorem 4.47: the selector-lift right-hand side is `0` except for the selector-sum
rows encoding `∑ δᵢ = 1` as two inequalities. -/
private def selectorConeLiftRhs
    {n k t : ℕ}
    (m : Fin k → ℕ) :
    SelectorConeLiftRow (n := n) (t := t) m → ℚ
  | .selectorSumLe => 1
  | .selectorSumGe => -1
  | _ => 0

/-- Helper for Theorem 4.47: reindex the selector-lift row type by `Fin` so it can serve as the
row index of the rational mixed witness matrices. -/
private noncomputable def selectorConeWitnessRowEquiv
    {n k t : ℕ}
    (m : Fin k → ℕ) :
    SelectorConeLiftRow (n := n) (t := t) m ≃
      Fin (Fintype.card (SelectorConeLiftRow (n := n) (t := t) m)) :=
  Fintype.equivFin (SelectorConeLiftRow (n := n) (t := t) m)

/-- Helper for Theorem 4.47: the integer-coefficient matrix of the selector/cone witness
polyhedron. -/
private noncomputable def selectorConeWitnessIntMatrix
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ) :
    Matrix (Fin (Fintype.card (SelectorConeLiftRow (n := n) (t := t) m))) (Fin (k + t)) ℚ := fun row j ↦
      selectorConeLiftIntCoeff m b r ((selectorConeWitnessRowEquiv m).symm row) j

/-- Helper for Theorem 4.47: the real-coefficient matrix of the selector/cone witness
polyhedron. -/
private noncomputable def selectorConeWitnessRealMatrix
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ) :
    Matrix (Fin (Fintype.card (SelectorConeLiftRow (n := n) (t := t) m)))
      (Fin (n + selectorConeRealAuxDim k n)) ℚ := fun row a ↦
        selectorConeLiftRealCoeff m A ((selectorConeWitnessRowEquiv m).symm row) a

/-- Helper for Theorem 4.47: the right-hand side vector of the selector/cone witness
polyhedron. -/
private noncomputable def selectorConeWitnessRhs
    {n k t : ℕ}
    (m : Fin k → ℕ) :
    Fin (Fintype.card (SelectorConeLiftRow (n := n) (t := t) m)) → ℚ := fun row ↦
      selectorConeLiftRhs m ((selectorConeWitnessRowEquiv m).symm row)

/-- Helper for Theorem 4.47: a singleton-weighted finite sum collapses to its active coordinate. -/
private lemma sumCastIteMul_eq_active
    {k : ℕ}
    (f : Fin k → ℝ)
    (i : Fin k)
    (c : ℚ) :
    ∑ j : Fin k, (((if j = i then c else 0 : ℚ) : ℝ) * f j) = (c : ℝ) * f i := by
  -- Only the selected coordinate survives the singleton coefficient family.
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Helper for Theorem 4.47: a flattened selector-part coefficient family that only sees one
outer block recovers the corresponding component sum. -/
private lemma sumFlattenSelectorParts_eq_component
    {n k : ℕ}
    (xParts : Fin k → Fin n → ℝ)
    (i : Fin k)
    (c : Fin n → ℚ) :
    ∑ a : Fin (selectorConeRealAuxDim k n),
        (((if (selectorConeFlatIndex a).1 = i then
            c (selectorConeFlatIndex a).2 else 0 : ℚ) : ℝ) *
          flattenSelectorParts xParts a) =
      ∑ l : Fin n, (c l : ℝ) * xParts i l := by
  let e : (Fin k × Fin n) ≃ Fin (selectorConeRealAuxDim k n) := Fintype.equivFin (Fin k × Fin n)
  calc
    ∑ a : Fin (selectorConeRealAuxDim k n),
        (((if (selectorConeFlatIndex a).1 = i then
            c (selectorConeFlatIndex a).2 else 0 : ℚ) : ℝ) *
          flattenSelectorParts xParts a) =
      ∑ ij : Fin k × Fin n, (((if ij.1 = i then c ij.2 else 0 : ℚ) : ℝ) * xParts ij.1 ij.2) := by
            exact Fintype.sum_equiv e.symm
              (fun a : Fin (selectorConeRealAuxDim k n) ↦
                (((if (selectorConeFlatIndex a).1 = i then
                    c (selectorConeFlatIndex a).2 else 0 : ℚ) : ℝ) *
                  flattenSelectorParts xParts a))
              (fun ij : Fin k × Fin n ↦ (((if ij.1 = i then c ij.2 else 0 : ℚ) : ℝ) * xParts ij.1 ij.2))
              (fun a ↦ by
                rfl)
    _ = ∑ l : Fin n, (c l : ℝ) * xParts i l := by
          rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
          · simp
          · intro i' _ hi'
            simp [hi']
          · simp

/-- Helper for Theorem 4.47: a flattened selector-part coefficient family that only sees one
visible coordinate sums that coordinate across all copied part blocks. -/
private lemma sumFlattenSelectorParts_eq_coordinate
    {n k : ℕ}
    (xParts : Fin k → Fin n → ℝ)
    (l : Fin n)
    (c : ℚ) :
    ∑ a : Fin (selectorConeRealAuxDim k n),
        (((if (selectorConeFlatIndex a).2 = l then c else 0 : ℚ) : ℝ) *
          flattenSelectorParts xParts a) =
      ∑ i : Fin k, (c : ℝ) * xParts i l := by
  let e : (Fin k × Fin n) ≃ Fin (selectorConeRealAuxDim k n) := Fintype.equivFin (Fin k × Fin n)
  calc
    ∑ a : Fin (selectorConeRealAuxDim k n),
        (((if (selectorConeFlatIndex a).2 = l then c else 0 : ℚ) : ℝ) *
          flattenSelectorParts xParts a) =
      ∑ ij : Fin k × Fin n, (((if ij.2 = l then c else 0 : ℚ) : ℝ) * xParts ij.1 ij.2) := by
            exact Fintype.sum_equiv e.symm
              (fun a : Fin (selectorConeRealAuxDim k n) ↦
                (((if (selectorConeFlatIndex a).2 = l then c else 0 : ℚ) : ℝ) *
                  flattenSelectorParts xParts a))
              (fun ij : Fin k × Fin n ↦ (((if ij.2 = l then c else 0 : ℚ) : ℝ) * xParts ij.1 ij.2))
              (fun a ↦ by
                rfl)
    _ = ∑ i : Fin k, (c : ℝ) * xParts i l := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using sumCastIteMul_eq_active (xParts i) l c

/-- Helper for Theorem 4.47: splitting and recombining the selector/cone integer block recovers
the original integer-coordinate vector. -/
private theorem selectorConeIntegerBlock_eta
    {k t : ℕ}
    (z : Fin (k + t) → ℝ) :
    Fin.append (fun i : Fin k ↦ z (Fin.castAdd t i)) (fun j : Fin t ↦ z (Fin.natAdd k j)) = z := by
  -- `Fin.append` is the canonical inverse to splitting the sum index by `castAdd` and `natAdd`.
  funext u
  refine Fin.addCases ?_ ?_ u
  · intro i
    simp
  · intro j
    simp

/-- Helper for Theorem 4.47: splitting the visible `x`-block and the flattened part block and then
recombining them recovers the original real-coordinate vector. -/
private theorem selectorConeRealBlock_eta
    {n k : ℕ}
    (w : Fin (n + selectorConeRealAuxDim k n) → ℝ) :
    Fin.append
        (fun i : Fin n ↦ w (Fin.castAdd (selectorConeRealAuxDim k n) i))
        (flattenSelectorParts
          (unflattenSelectorParts
            (fun a : Fin (selectorConeRealAuxDim k n) ↦ w (Fin.natAdd n a)))) = w := by
  -- The second block is just `w` reindexed through the flatten/unflatten equivalence.
  funext u
  refine Fin.addCases ?_ ?_ u
  · intro i
    simp
  · intro a
    simp [flattenSelectorParts, unflattenSelectorParts]

/-- Helper for Theorem 4.47: each scaled polytope constraint
`(A i).map (Rat.castHom ℝ) *ᵥ xParts i ≤ δ i • b i` can be rewritten as a selector-lift row with
right-hand side `0`. -/
private lemma selectorConeComponentRow_le_zero
    {n k : ℕ}
    {m : Fin k → ℕ}
    {A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ}
    {b : ∀ i : Fin k, Fin (m i) → ℚ}
    {xParts : Fin k → Fin n → ℝ}
    {δ : Fin k → ℝ}
    (hineq : ∀ i : Fin k,
      (A i).map (Rat.castHom ℝ) *ᵥ xParts i ≤
        δ i • (fun j : Fin (m i) ↦ (b i j : ℝ)))
    (i : Fin k)
    (s : Fin (m i)) :
    ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s +
        (((-(b i s) : ℚ) : ℝ) * δ i) ≤
      0 := by
  -- Read the scaled right-hand side at coordinate `s`, then move it to the left-hand side.
  have hs : ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s ≤ δ i * (b i s : ℝ) := by
    simpa [Pi.smul_apply] using hineq i s
  have hs' :
      ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s +
          -(δ i * (b i s : ℝ)) ≤
        0 := by
    linarith
  have hrewrite :
      ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s +
          (((-(b i s) : ℚ) : ℝ) * δ i) =
        ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s +
          -(δ i * (b i s : ℝ)) := by
    calc
      ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s + (((-(b i s) : ℚ) : ℝ) * δ i)
          =
            ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s + (-((b i s : ℝ) * δ i)) := by
              simp
      _ = ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s + -(δ i * (b i s : ℝ)) := by
            rw [mul_comm]
  rw [hrewrite]
  exact hs'

/-- Helper for Theorem 4.47: the reconstruction equality in the selector lift becomes a
coordinatewise equality `x l = ∑ i, xParts i l + ∑ j, μ j * r_jl`. -/
private lemma selectorConeCoordinateReconstruction
    {n k t : ℕ}
    {x : Fin n → ℝ}
    {xParts : Fin k → Fin n → ℝ}
    {μ : Fin t → ℝ}
    {r : Fin t → Fin n → ℤ}
    (hxeq :
      x = (∑ i : Fin k, xParts i) + ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ)))
    (l : Fin n) :
    x l = ∑ i : Fin k, xParts i l + ∑ j : Fin t, μ j * (r j l : ℝ) := by
  -- Evaluate the functional equality at coordinate `l` and unfold the scalar action.
  simpa [Pi.add_apply, Finset.sum_apply, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using congrFun hxeq l

/-- Helper for Theorem 4.47: evaluating a component selector row on the packed lift recovers the
scaled polytope inequality left-hand side. -/
private lemma selectorConePackedComponentRow_eval
    {n k t : ℕ}
    {m : Fin k → ℕ}
    {A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ}
    {b : ∀ i : Fin k, Fin (m i) → ℚ}
    {r : Fin t → Fin n → ℤ}
    {x : Fin n → ℝ}
    {xParts : Fin k → Fin n → ℝ}
    {δ : Fin k → ℝ}
    {μ : Fin t → ℝ}
    (i : Fin k)
    (s : Fin (m i)) :
    (fun j ↦
      ((selectorConeLiftIntCoeff m b r
        (SelectorConeLiftRow.component (n := n) (t := t) i s) j : ℚ) : ℝ)) ⬝ᵥ
        (Fin.append δ μ) +
        (fun a ↦
          ((selectorConeLiftRealCoeff m A
            (SelectorConeLiftRow.component (n := n) (t := t) i s) a : ℚ) : ℝ)) ⬝ᵥ
            (Fin.append x (flattenSelectorParts xParts)) =
      ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s + (((-(b i s) : ℚ) : ℝ) * δ i) := by
  -- Split the appended blocks and collapse the singleton-supported selector coefficients.
  rw [dotProduct, dotProduct, Fin.sum_univ_add, Fin.sum_univ_add]
  simp [selectorConeLiftIntCoeff, selectorConeLiftRealCoeff]
  rw [sumCastIteMul_eq_active δ i (-(b i s)),
    sumFlattenSelectorParts_eq_component xParts i (fun l ↦ A i s l)]
  simp [Matrix.mulVec, dotProduct, add_comm, add_left_comm, add_assoc]

/-- Helper for Theorem 4.47: evaluating the `x ≤ ∑ xⁱ + ∑ μⱼ rʲ` row on the packed lift gives the
corresponding coordinate residual. -/
private lemma selectorConePackedXEqLeRow_eval
    {n k t : ℕ}
    {m : Fin k → ℕ}
    {A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ}
    {b : ∀ i : Fin k, Fin (m i) → ℚ}
    {r : Fin t → Fin n → ℤ}
    {x : Fin n → ℝ}
    {xParts : Fin k → Fin n → ℝ}
    {δ : Fin k → ℝ}
    {μ : Fin t → ℝ}
    (l : Fin n) :
    (fun j ↦
      ((selectorConeLiftIntCoeff m b r
        (SelectorConeLiftRow.xEqLe (n := n) (t := t) l) j : ℚ) : ℝ)) ⬝ᵥ
        (Fin.append δ μ) +
    (fun a ↦
          ((selectorConeLiftRealCoeff m A
            (SelectorConeLiftRow.xEqLe (n := n) (t := t) l) a : ℚ) : ℝ)) ⬝ᵥ
            (Fin.append x (flattenSelectorParts xParts)) =
      x l - (∑ i : Fin k, xParts i l) - ∑ j : Fin t, μ j * (r j l : ℝ) := by
  -- Normalize the integer, visible-`x`, and flattened-part blocks separately before collecting
  -- them into the displayed coordinate residual.
  rw [dotProduct, dotProduct, Fin.sum_univ_add, Fin.sum_univ_add]
  simp [selectorConeLiftIntCoeff, selectorConeLiftRealCoeff]
  rw [sumCastIteMul_eq_active x l 1,
    sumFlattenSelectorParts_eq_coordinate xParts l (-1)]
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 4.47: evaluating the `x ≥ ∑ xⁱ + ∑ μⱼ rʲ` row on the packed lift gives the
opposite coordinate residual. -/
private lemma selectorConePackedXEqGeRow_eval
    {n k t : ℕ}
    {m : Fin k → ℕ}
    {A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ}
    {b : ∀ i : Fin k, Fin (m i) → ℚ}
    {r : Fin t → Fin n → ℤ}
    {x : Fin n → ℝ}
    {xParts : Fin k → Fin n → ℝ}
    {δ : Fin k → ℝ}
    {μ : Fin t → ℝ}
    (l : Fin n) :
    (fun j ↦
      ((selectorConeLiftIntCoeff m b r
        (SelectorConeLiftRow.xEqGe (n := n) (t := t) l) j : ℚ) : ℝ)) ⬝ᵥ
        (Fin.append δ μ) +
    (fun a ↦
          ((selectorConeLiftRealCoeff m A
            (SelectorConeLiftRow.xEqGe (n := n) (t := t) l) a : ℚ) : ℝ)) ⬝ᵥ
            (Fin.append x (flattenSelectorParts xParts)) =
      -x l + (∑ i : Fin k, xParts i l) + ∑ j : Fin t, μ j * (r j l : ℝ) := by
  -- Normalize the same three blocks as above, but keep the opposite signs coming from the
  -- `xEqGe` row coefficients.
  rw [dotProduct, dotProduct, Fin.sum_univ_add, Fin.sum_univ_add]
  simp [selectorConeLiftIntCoeff, selectorConeLiftRealCoeff]
  rw [sumCastIteMul_eq_active x l (-1),
    sumFlattenSelectorParts_eq_coordinate xParts l 1]
  simp [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 4.47: evaluating the selector-sum upper row on the packed lift returns the
selector total `∑ i, δ i`. -/
private lemma selectorConePackedSelectorSumLeRow_eval
    {n k t : ℕ}
    {m : Fin k → ℕ}
    {A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ}
    {b : ∀ i : Fin k, Fin (m i) → ℚ}
    {r : Fin t → Fin n → ℤ}
    {x : Fin n → ℝ}
    {xParts : Fin k → Fin n → ℝ}
    {δ : Fin k → ℝ}
    {μ : Fin t → ℝ} :
    (fun j ↦
      ((selectorConeLiftIntCoeff m b r
        (SelectorConeLiftRow.selectorSumLe (n := n) (t := t)) j : ℚ) : ℝ)) ⬝ᵥ
        (Fin.append δ μ) +
        (fun a ↦
          ((selectorConeLiftRealCoeff m A
            (SelectorConeLiftRow.selectorSumLe (n := n) (t := t)) a : ℚ) : ℝ)) ⬝ᵥ
            (Fin.append x (flattenSelectorParts xParts)) =
      ∑ i : Fin k, δ i := by
  -- Only the selector block contributes to the selector-sum row.
  rw [dotProduct, dotProduct, Fin.sum_univ_add, Fin.sum_univ_add]
  simp [selectorConeLiftIntCoeff, selectorConeLiftRealCoeff]

/-- Helper for Theorem 4.47: evaluating the selector-sum lower row on the packed lift returns the
negated selector total `-∑ i, δ i`. -/
private lemma selectorConePackedSelectorSumGeRow_eval
    {n k t : ℕ}
    {m : Fin k → ℕ}
    {A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ}
    {b : ∀ i : Fin k, Fin (m i) → ℚ}
    {r : Fin t → Fin n → ℤ}
    {x : Fin n → ℝ}
    {xParts : Fin k → Fin n → ℝ}
    {δ : Fin k → ℝ}
    {μ : Fin t → ℝ} :
    (fun j ↦
      ((selectorConeLiftIntCoeff m b r
        (SelectorConeLiftRow.selectorSumGe (n := n) (t := t)) j : ℚ) : ℝ)) ⬝ᵥ
        (Fin.append δ μ) +
        (fun a ↦
          ((selectorConeLiftRealCoeff m A
            (SelectorConeLiftRow.selectorSumGe (n := n) (t := t)) a : ℚ) : ℝ)) ⬝ᵥ
            (Fin.append x (flattenSelectorParts xParts)) =
      -(∑ i : Fin k, δ i) := by
  -- The lower selector-sum row differs only by an overall sign.
  rw [dotProduct, dotProduct, Fin.sum_univ_add, Fin.sum_univ_add]
  simp [selectorConeLiftIntCoeff, selectorConeLiftRealCoeff]

/-- Helper for Theorem 4.47: evaluating a selector nonnegativity row on the packed lift returns
the negated selector coordinate. -/
private lemma selectorConePackedDeltaNonnegRow_eval
    {n k t : ℕ}
    {m : Fin k → ℕ}
    {A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ}
    {b : ∀ i : Fin k, Fin (m i) → ℚ}
    {r : Fin t → Fin n → ℤ}
    {x : Fin n → ℝ}
    {xParts : Fin k → Fin n → ℝ}
    {δ : Fin k → ℝ}
    {μ : Fin t → ℝ}
    (i : Fin k) :
    (fun j ↦
      ((selectorConeLiftIntCoeff m b r
        (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i) j : ℚ) : ℝ)) ⬝ᵥ
          (Fin.append δ μ) +
        (fun a ↦
          ((selectorConeLiftRealCoeff m A
            (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i) a : ℚ) : ℝ)) ⬝ᵥ
            (Fin.append x (flattenSelectorParts xParts)) =
      -δ i := by
  -- Only the selected `δ i` coordinate appears in this row.
  rw [dotProduct, dotProduct, Fin.sum_univ_add, Fin.sum_univ_add]
  simp [selectorConeLiftIntCoeff, selectorConeLiftRealCoeff, sumCastIteMul_eq_active]

/-- Helper for Theorem 4.47: evaluating a cone-coefficient nonnegativity row on the packed lift
returns the negated cone coordinate. -/
private lemma selectorConePackedMuNonnegRow_eval
    {n k t : ℕ}
    {m : Fin k → ℕ}
    {A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ}
    {b : ∀ i : Fin k, Fin (m i) → ℚ}
    {r : Fin t → Fin n → ℤ}
    {x : Fin n → ℝ}
    {xParts : Fin k → Fin n → ℝ}
    {δ : Fin k → ℝ}
    {μ : Fin t → ℝ}
    (j : Fin t) :
    (fun i ↦
      ((selectorConeLiftIntCoeff m b r
        (SelectorConeLiftRow.muNonneg (n := n) (t := t) j) i : ℚ) : ℝ)) ⬝ᵥ
        (Fin.append δ μ) +
        (fun a ↦
          ((selectorConeLiftRealCoeff m A
            (SelectorConeLiftRow.muNonneg (n := n) (t := t) j) a : ℚ) : ℝ)) ⬝ᵥ
            (Fin.append x (flattenSelectorParts xParts)) =
      -μ j := by
  -- Only the selected `μ j` coordinate appears in this row.
  rw [dotProduct, dotProduct, Fin.sum_univ_add, Fin.sum_univ_add]
  simp [selectorConeLiftIntCoeff, selectorConeLiftRealCoeff, sumCastIteMul_eq_active]

/-- Helper for Theorem 4.47: the selector/cone converse witness as a rational mixed polyhedron
whose integer block stores `(δ, μ)` and whose real block stores `(x, flatten xParts)`. -/
private noncomputable def selectorConeWitnessPolyhedron
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ) :
    Set (MixedRealPoint (k + t) (n + selectorConeRealAuxDim k n)) :=
  rational_mixed_polyhedron
    (selectorConeWitnessIntMatrix m b r)
    (selectorConeWitnessRealMatrix m A)
    (selectorConeWitnessRhs m)

/-- Helper for Theorem 4.47: `selectorConeWitnessPolyhedron m A b r` is rational mixed polyhedral
because it is defined by the explicit selector/cone coefficient matrices. -/
private theorem selectorConeWitnessPolyhedron_isRationalMixedPolyhedron
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ) :
    is_rational_mixed_polyhedron (selectorConeWitnessPolyhedron m A b r) := by
  refine (is_rational_mixed_polyhedron_iff).2 ?_
  exact ⟨Fintype.card (SelectorConeLiftRow (n := n) (t := t) m), selectorConeWitnessIntMatrix m b r,
    selectorConeWitnessRealMatrix m A, selectorConeWitnessRhs m, rfl⟩

/-- Helper for Theorem 4.47: the canonical selector/cone witness projects to exactly the union of
the rational matrix polytope pieces translated by the common integral cone. -/
private theorem mem_selectorConeWitnessProjection_iff
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ)
    (hPoly : ∀ i : Fin k, (rational_matrix_polyhedron (A i) (b i)).IsRationalPolytope)
    (hNonempty : ∀ i : Fin k, (rational_matrix_polyhedron (A i) (b i)).Nonempty)
    {x : Fin n → ℝ} :
    x ∈ mixed_integer_x_projection (selectorConeWitnessPolyhedron m A b r) ↔
      x ∈ (⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)) + integral_intcone r := by
  classical
  let rowEquiv :
      SelectorConeLiftRow (n := n) (t := t) m ≃
        Fin (Fintype.card (SelectorConeLiftRow (n := n) (t := t) m)) :=
    selectorConeWitnessRowEquiv m
  let intMatrix :
      Matrix (Fin (Fintype.card (SelectorConeLiftRow (n := n) (t := t) m)))
        (Fin (k + t)) ℚ := fun row j ↦
          selectorConeLiftIntCoeff m b r (rowEquiv.symm row) j
  let realMatrix :
      Matrix (Fin (Fintype.card (SelectorConeLiftRow (n := n) (t := t) m)))
        (Fin (n + selectorConeRealAuxDim k n)) ℚ := fun row a ↦
          selectorConeLiftRealCoeff m A (rowEquiv.symm row) a
  let rhs :
      Fin (Fintype.card (SelectorConeLiftRow (n := n) (t := t) m)) → ℚ := fun row ↦
        selectorConeLiftRhs m (rowEquiv.symm row)
  rw [mem_mixed_integer_x_projection_iff]
  constructor
  · rintro ⟨y, z, hzWitness⟩
    have hz :
        ((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ)) +
            (realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y) ≤
          fun row ↦ (rhs row : ℝ) := by
      rw [selectorConeWitnessPolyhedron, mem_rational_mixed_polyhedron_iff] at hzWitness
      simpa [selectorConeWitnessIntMatrix, selectorConeWitnessRealMatrix, selectorConeWitnessRhs,
        selectorConeWitnessRowEquiv, rowEquiv, intMatrix, realMatrix, rhs] using hzWitness
    let xParts : Fin k → Fin n → ℝ := unflattenSelectorParts y
    let δInt : Fin k → ℤ := fun i ↦ z (Fin.castAdd t i)
    let μInt : Fin t → ℤ := fun j ↦ z (Fin.natAdd k j)
    have hIntEta :
        Fin.append (fun i : Fin k ↦ (δInt i : ℝ)) (fun j : Fin t ↦ (μInt j : ℝ)) =
          fun j : Fin (k + t) ↦ (z j : ℝ) := by
      funext j
      refine Fin.addCases ?_ ?_ j
      · intro i
        simp [δInt]
      · intro j
        simp [μInt]
    have hRealEta :
        Fin.append x (flattenSelectorParts xParts) = Fin.append x y := by
      simp [xParts, flattenSelectorParts_unflattenSelectorParts]
    have hComponentEval :
        ∀ (i : Fin k) (s : Fin (m i)),
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              (rowEquiv (SelectorConeLiftRow.component (n := n) (t := t) i s)) =
            ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s + (((-(b i s) : ℚ) : ℝ) * (δInt i : ℝ)) := by
      intro i s
      simpa [intMatrix, realMatrix, rowEquiv, Matrix.mulVec, dotProduct, hIntEta, hRealEta,
        add_comm, add_left_comm, add_assoc] using
        (selectorConePackedComponentRow_eval (A := A) (b := b) (r := r) (x := x)
          (xParts := xParts) (δ := fun i ↦ (δInt i : ℝ)) (μ := fun j ↦ (μInt j : ℝ)) i s)
    have hXEqLeEval :
        ∀ l : Fin n,
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              (rowEquiv (SelectorConeLiftRow.xEqLe (n := n) (t := t) l)) =
            x l - (∑ i : Fin k, xParts i l) - ∑ j : Fin t, (μInt j : ℝ) * (r j l : ℝ) := by
      intro l
      simpa [intMatrix, realMatrix, rowEquiv, Matrix.mulVec, dotProduct, hIntEta, hRealEta,
        add_comm, add_left_comm, add_assoc] using
        (selectorConePackedXEqLeRow_eval (A := A) (b := b) (r := r) (x := x)
          (xParts := xParts) (δ := fun i ↦ (δInt i : ℝ)) (μ := fun j ↦ (μInt j : ℝ)) l)
    have hXEqGeEval :
        ∀ l : Fin n,
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              (rowEquiv (SelectorConeLiftRow.xEqGe (n := n) (t := t) l)) =
            -x l + (∑ i : Fin k, xParts i l) + ∑ j : Fin t, (μInt j : ℝ) * (r j l : ℝ) := by
      intro l
      simpa [intMatrix, realMatrix, rowEquiv, Matrix.mulVec, dotProduct, hIntEta, hRealEta,
        add_comm, add_left_comm, add_assoc] using
        (selectorConePackedXEqGeRow_eval (A := A) (b := b) (r := r) (x := x)
          (xParts := xParts) (δ := fun i ↦ (δInt i : ℝ)) (μ := fun j ↦ (μInt j : ℝ)) l)
    have hSelectorSumLeEval :
        (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
            ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
            (rowEquiv (SelectorConeLiftRow.selectorSumLe (n := n) (t := t))) =
          ∑ i : Fin k, (δInt i : ℝ) := by
      simpa [intMatrix, realMatrix, rowEquiv, Matrix.mulVec, dotProduct, hIntEta, hRealEta,
        add_comm, add_left_comm, add_assoc] using
        (selectorConePackedSelectorSumLeRow_eval (A := A) (b := b) (r := r) (x := x)
          (xParts := xParts) (δ := fun i ↦ (δInt i : ℝ)) (μ := fun j ↦ (μInt j : ℝ)))
    have hSelectorSumGeEval :
        (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
            ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
            (rowEquiv (SelectorConeLiftRow.selectorSumGe (n := n) (t := t))) =
          -(∑ i : Fin k, (δInt i : ℝ)) := by
      simpa [intMatrix, realMatrix, rowEquiv, Matrix.mulVec, dotProduct, hIntEta, hRealEta,
        add_comm, add_left_comm, add_assoc] using
        (selectorConePackedSelectorSumGeRow_eval (A := A) (b := b) (r := r) (x := x)
          (xParts := xParts) (δ := fun i ↦ (δInt i : ℝ)) (μ := fun j ↦ (μInt j : ℝ)))
    have hDeltaNonnegEval :
        ∀ i : Fin k,
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              (rowEquiv (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i)) =
            -((δInt i : ℝ)) := by
      intro i
      simpa [intMatrix, realMatrix, rowEquiv, Matrix.mulVec, dotProduct, hIntEta, hRealEta,
        add_comm, add_left_comm, add_assoc] using
        (selectorConePackedDeltaNonnegRow_eval (A := A) (b := b) (r := r) (x := x)
          (xParts := xParts) (δ := fun i ↦ (δInt i : ℝ)) (μ := fun j ↦ (μInt j : ℝ)) i)
    have hMuNonnegEval :
        ∀ j : Fin t,
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j' : Fin (k + t) ↦ (z j' : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              (rowEquiv (SelectorConeLiftRow.muNonneg (n := n) (t := t) j)) =
            -((μInt j : ℝ)) := by
      intro j
      simpa [intMatrix, realMatrix, rowEquiv, Matrix.mulVec, dotProduct, hIntEta, hRealEta,
        add_comm, add_left_comm, add_assoc] using
        (selectorConePackedMuNonnegRow_eval (A := A) (b := b) (r := r) (x := x)
          (xParts := xParts) (δ := fun i ↦ (δInt i : ℝ)) (μ := fun j ↦ (μInt j : ℝ)) j)
    have hineq :
        ∀ i : Fin k,
          (A i).map (Rat.castHom ℝ) *ᵥ xParts i ≤
            (δInt i : ℝ) • (fun j : Fin (m i) ↦ (b i j : ℝ)) := by
      intro i s
      have hrow :
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              (rowEquiv (SelectorConeLiftRow.component (n := n) (t := t) i s)) ≤
            (rhs (rowEquiv (SelectorConeLiftRow.component (n := n) (t := t) i s)) : ℝ) :=
        hz (rowEquiv (SelectorConeLiftRow.component (n := n) (t := t) i s))
      have hrowZero :
          ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s + (((-(b i s) : ℚ) : ℝ) * (δInt i : ℝ)) ≤ 0 := by
        calc
          ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s + (((-(b i s) : ℚ) : ℝ) * (δInt i : ℝ))
              =
            (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
                (rowEquiv (SelectorConeLiftRow.component (n := n) (t := t) i s)) := (hComponentEval i s).symm
          _ ≤ (rhs (rowEquiv (SelectorConeLiftRow.component (n := n) (t := t) i s)) : ℝ) := hrow
          _ = 0 := by simp [rhs, rowEquiv, selectorConeLiftRhs]
      have hrowZero' :
          ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s - (δInt i : ℝ) * (b i s : ℝ) ≤ 0 := by
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hrowZero
      have hs :
          ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s ≤ (δInt i : ℝ) * (b i s : ℝ) := by
        linarith [hrowZero']
      simpa [Pi.smul_apply] using hs
    have hxeq :
        x =
          (∑ i : Fin k, xParts i) +
            ∑ j : Fin t, (μInt j : ℝ) • (fun l : Fin n ↦ (r j l : ℝ)) := by
      ext l
      have hrowLe :
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              (rowEquiv (SelectorConeLiftRow.xEqLe (n := n) (t := t) l)) ≤
            (rhs (rowEquiv (SelectorConeLiftRow.xEqLe (n := n) (t := t) l)) : ℝ) :=
        hz (rowEquiv (SelectorConeLiftRow.xEqLe (n := n) (t := t) l))
      have hrowGe :
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              (rowEquiv (SelectorConeLiftRow.xEqGe (n := n) (t := t) l)) ≤
            (rhs (rowEquiv (SelectorConeLiftRow.xEqGe (n := n) (t := t) l)) : ℝ) :=
        hz (rowEquiv (SelectorConeLiftRow.xEqGe (n := n) (t := t) l))
      have hle :
          x l - (∑ i : Fin k, xParts i l) - ∑ j : Fin t, (μInt j : ℝ) * (r j l : ℝ) ≤ 0 := by
        calc
          x l - (∑ i : Fin k, xParts i l) - ∑ j : Fin t, (μInt j : ℝ) * (r j l : ℝ)
              =
            (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
                (rowEquiv (SelectorConeLiftRow.xEqLe (n := n) (t := t) l)) := (hXEqLeEval l).symm
          _ ≤ (rhs (rowEquiv (SelectorConeLiftRow.xEqLe (n := n) (t := t) l)) : ℝ) := hrowLe
          _ = 0 := by simp [rhs, rowEquiv, selectorConeLiftRhs]
      have hge :
          -x l + (∑ i : Fin k, xParts i l) + ∑ j : Fin t, (μInt j : ℝ) * (r j l : ℝ) ≤ 0 := by
        calc
          -x l + (∑ i : Fin k, xParts i l) + ∑ j : Fin t, (μInt j : ℝ) * (r j l : ℝ)
              =
            (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
                (rowEquiv (SelectorConeLiftRow.xEqGe (n := n) (t := t) l)) := (hXEqGeEval l).symm
          _ ≤ (rhs (rowEquiv (SelectorConeLiftRow.xEqGe (n := n) (t := t) l)) : ℝ) := hrowGe
          _ = 0 := by simp [rhs, rowEquiv, selectorConeLiftRhs]
      have hx_le : x l ≤ ∑ i : Fin k, xParts i l + ∑ j : Fin t, (μInt j : ℝ) * (r j l : ℝ) := by
        linarith [hle]
      have hx_ge : ∑ i : Fin k, xParts i l + ∑ j : Fin t, (μInt j : ℝ) * (r j l : ℝ) ≤ x l := by
        linarith [hge]
      simpa [Pi.add_apply, Finset.sum_apply, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using le_antisymm hx_le hx_ge
    have hδsum : ∑ i : Fin k, (δInt i : ℝ) = 1 := by
      let rowSelLe := rowEquiv (SelectorConeLiftRow.selectorSumLe (n := n) (t := t))
      let rowSelGe := rowEquiv (SelectorConeLiftRow.selectorSumGe (n := n) (t := t))
      have hrowLe :
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              rowSelLe ≤
            (rhs rowSelLe : ℝ) := hz rowSelLe
      have hrowGe :
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              rowSelGe ≤
            (rhs rowSelGe : ℝ) := hz rowSelGe
      have hle : ∑ i : Fin k, (δInt i : ℝ) ≤ 1 := by
        calc
          ∑ i : Fin k, (δInt i : ℝ) =
            (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y)) rowSelLe :=
              hSelectorSumLeEval.symm
          _ ≤ (rhs rowSelLe : ℝ) := hrowLe
          _ = 1 := by simp [rowSelLe, rhs, rowEquiv, selectorConeLiftRhs]
      have hge : -(∑ i : Fin k, (δInt i : ℝ)) ≤ -1 := by
        calc
          -(∑ i : Fin k, (δInt i : ℝ)) =
            (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y)) rowSelGe :=
              hSelectorSumGeEval.symm
          _ ≤ (rhs rowSelGe : ℝ) := hrowGe
          _ = -1 := by simp [rowSelGe, rhs, rowEquiv, selectorConeLiftRhs]
      linarith
    have hδnonneg : ∀ i : Fin k, 0 ≤ (δInt i : ℝ) := by
      intro i
      have hrow :
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              (rowEquiv (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i)) ≤
            (rhs (rowEquiv (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i)) : ℝ) :=
        hz (rowEquiv (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i))
      have hnonneg : -((δInt i : ℝ)) ≤ 0 := by
        calc
          -((δInt i : ℝ)) =
            (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j : Fin (k + t) ↦ (z j : ℝ))) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
                (rowEquiv (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i)) := (hDeltaNonnegEval i).symm
          _ ≤ (rhs (rowEquiv (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i)) : ℝ) := hrow
          _ = 0 := by simp [rhs, rowEquiv, selectorConeLiftRhs]
      linarith
    have hμnonneg : ∀ j : Fin t, 0 ≤ (μInt j : ℝ) := by
      intro j
      have hrow :
          (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j' : Fin (k + t) ↦ (z j' : ℝ))) +
              ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
              (rowEquiv (SelectorConeLiftRow.muNonneg (n := n) (t := t) j)) ≤
            (rhs (rowEquiv (SelectorConeLiftRow.muNonneg (n := n) (t := t) j)) : ℝ) :=
        hz (rowEquiv (SelectorConeLiftRow.muNonneg (n := n) (t := t) j))
      have hnonneg : -((μInt j : ℝ)) ≤ 0 := by
        calc
          -((μInt j : ℝ)) =
            (((intMatrix.map (Rat.castHom ℝ)) *ᵥ (fun j' : Fin (k + t) ↦ (z j' : ℝ))) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x y))
                (rowEquiv (SelectorConeLiftRow.muNonneg (n := n) (t := t) j)) := (hMuNonnegEval j).symm
          _ ≤ (rhs (rowEquiv (SelectorConeLiftRow.muNonneg (n := n) (t := t) j)) : ℝ) := hrow
          _ = 0 := by simp [rhs, rowEquiv, selectorConeLiftRhs]
      linarith
    have hδInt_nonneg : ∀ i : Fin k, 0 ≤ δInt i := by
      intro i
      exact_mod_cast hδnonneg i
    have hμInt_nonneg : ∀ j : Fin t, 0 ≤ μInt j := by
      intro j
      exact_mod_cast hμnonneg j
    let δNat : Fin k → ℕ := fun i ↦ Int.toNat (δInt i)
    let μNat : Fin t → ℕ := fun j ↦ Int.toNat (μInt j)
    have hδNatCast : ∀ i : Fin k, ((δNat i : ℕ) : ℝ) = (δInt i : ℝ) := by
      intro i
      have hcastInt : (((δNat i : ℕ) : ℤ)) = δInt i := by
        simp [δNat, Int.toNat_of_nonneg (hδInt_nonneg i)]
      exact_mod_cast hcastInt
    have hμNatCast : ∀ j : Fin t, ((μNat j : ℕ) : ℝ) = (μInt j : ℝ) := by
      intro j
      have hcastInt : (((μNat j : ℕ) : ℤ)) = μInt j := by
        simp [μNat, Int.toNat_of_nonneg (hμInt_nonneg j)]
      exact_mod_cast hcastInt
    have hineqNat :
        ∀ i : Fin k,
          (A i).map (Rat.castHom ℝ) *ᵥ xParts i ≤
            (δNat i : ℝ) • (fun j : Fin (m i) ↦ (b i j : ℝ)) := by
      intro i
      rw [hδNatCast i]
      exact hineq i
    have hxeqNat :
        x =
          (∑ i : Fin k, xParts i) +
            ∑ j : Fin t, (μNat j : ℝ) • (fun l : Fin n ↦ (r j l : ℝ)) := by
      calc
        x =
            (∑ i : Fin k, xParts i) +
              ∑ j : Fin t, (μInt j : ℝ) • (fun l : Fin n ↦ (r j l : ℝ)) := hxeq
        _ =
            (∑ i : Fin k, xParts i) +
              ∑ j : Fin t, (μNat j : ℝ) • (fun l : Fin n ↦ (r j l : ℝ)) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [hμNatCast j]
    have hδsumInt : ∑ i : Fin k, δInt i = 1 := by
      exact_mod_cast hδsum
    have hδsumNat : ∑ i : Fin k, δNat i = 1 := by
      have hcast :
          (((∑ i : Fin k, δNat i : ℕ) : ℤ)) = 1 := by
        calc
          (((∑ i : Fin k, δNat i : ℕ) : ℤ)) = ∑ i : Fin k, δInt i := by
            simp [δNat, hδInt_nonneg]
          _ = 1 := hδsumInt
      exact_mod_cast hcast
    exact
      (mem_iUnion_rational_matrix_polyhedron_add_integral_intcone_iff_exists_oneHotLift
        hPoly hNonempty).2 ⟨xParts, δNat, μNat, hineqNat, hxeqNat, hδsumNat⟩
  · intro hx
    rcases
      (mem_iUnion_rational_matrix_polyhedron_add_integral_intcone_iff_exists_oneHotLift
        hPoly hNonempty).1 hx with
      ⟨xParts, δNat, μNat, hineq, hxeq, hδsum⟩
    let z : Fin (k + t) → ℤ := Fin.append (fun i ↦ (δNat i : ℤ)) (fun j ↦ (μNat j : ℤ))
    let zReal : Fin (k + t) → ℝ := fun j ↦ (z j : ℝ)
    have hzRealEta :
        zReal = Fin.append (fun i : Fin k ↦ (δNat i : ℝ)) (fun j : Fin t ↦ (μNat j : ℝ)) := by
      funext j
      refine Fin.addCases ?_ ?_ j
      · intro i
        simp [z, zReal]
      · intro j
        simp [z, zReal]
    have hz :
        ((intMatrix.map (Rat.castHom ℝ)) *ᵥ zReal +
            (realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x (flattenSelectorParts xParts)) ≤
          fun row ↦ (rhs row : ℝ) := by
      intro row
      cases hnative : rowEquiv.symm row with
      | component i s =>
          have hrowFin' :
              row = rowEquiv (SelectorConeLiftRow.component (n := n) (t := t) i s) := by
            calc
              row = rowEquiv (rowEquiv.symm row) := by
                symm
                exact Equiv.apply_symm_apply rowEquiv row
              _ = rowEquiv (SelectorConeLiftRow.component (n := n) (t := t) i s) := by
                    rw [hnative]
          rw [hrowFin']
          calc
            ((((intMatrix.map (Rat.castHom ℝ)) *ᵥ zReal) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x (flattenSelectorParts xParts)))
                (rowEquiv (SelectorConeLiftRow.component (n := n) (t := t) i s)))
                =
              ((A i).map (Rat.castHom ℝ) *ᵥ xParts i) s +
                (((-(b i s) : ℚ) : ℝ) * (δNat i : ℝ)) := by
                  simpa [intMatrix, realMatrix, rowEquiv, z, zReal, hzRealEta, Matrix.mulVec, dotProduct,
                    add_comm, add_left_comm, add_assoc] using
                    (selectorConePackedComponentRow_eval (A := A) (b := b) (r := r) (x := x)
                      (xParts := xParts) (δ := fun i ↦ (δNat i : ℝ))
                      (μ := fun j ↦ (μNat j : ℝ)) i s)
            _ ≤ 0 := selectorConeComponentRow_le_zero hineq i s
            _ = (rhs (rowEquiv (SelectorConeLiftRow.component (n := n) (t := t) i s)) : ℝ) := by
                  simp [rhs, rowEquiv, selectorConeLiftRhs]
      | xEqLe l =>
          have hrowFin' :
              row = rowEquiv (SelectorConeLiftRow.xEqLe (n := n) (t := t) l) := by
            calc
              row = rowEquiv (rowEquiv.symm row) := by
                symm
                exact Equiv.apply_symm_apply rowEquiv row
              _ = rowEquiv (SelectorConeLiftRow.xEqLe (n := n) (t := t) l) := by
                    rw [hnative]
          rw [hrowFin']
          have hcoord : x l = ∑ i : Fin k, xParts i l + ∑ j : Fin t, (μNat j : ℝ) * (r j l : ℝ) :=
            selectorConeCoordinateReconstruction hxeq l
          have hrowLe :
              x l - (∑ i : Fin k, xParts i l) - ∑ j : Fin t, (μNat j : ℝ) * (r j l : ℝ) ≤ 0 := by
            linarith
          calc
            ((((intMatrix.map (Rat.castHom ℝ)) *ᵥ zReal) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x (flattenSelectorParts xParts)))
                (rowEquiv (SelectorConeLiftRow.xEqLe (n := n) (t := t) l)))
                =
              x l - (∑ i : Fin k, xParts i l) - ∑ j : Fin t, (μNat j : ℝ) * (r j l : ℝ) := by
                  simpa [intMatrix, realMatrix, rowEquiv, z, zReal, hzRealEta, Matrix.mulVec, dotProduct,
                    add_comm, add_left_comm, add_assoc] using
                    (selectorConePackedXEqLeRow_eval (A := A) (b := b) (r := r) (x := x)
                      (xParts := xParts) (δ := fun i ↦ (δNat i : ℝ))
                      (μ := fun j ↦ (μNat j : ℝ)) l)
            _ ≤ 0 := hrowLe
            _ = (rhs (rowEquiv (SelectorConeLiftRow.xEqLe (n := n) (t := t) l)) : ℝ) := by
                  simp [rhs, rowEquiv, selectorConeLiftRhs]
      | xEqGe l =>
          have hrowFin' :
              row = rowEquiv (SelectorConeLiftRow.xEqGe (n := n) (t := t) l) := by
            calc
              row = rowEquiv (rowEquiv.symm row) := by
                symm
                exact Equiv.apply_symm_apply rowEquiv row
              _ = rowEquiv (SelectorConeLiftRow.xEqGe (n := n) (t := t) l) := by
                    rw [hnative]
          rw [hrowFin']
          have hcoord : x l = ∑ i : Fin k, xParts i l + ∑ j : Fin t, (μNat j : ℝ) * (r j l : ℝ) :=
            selectorConeCoordinateReconstruction hxeq l
          have hrowGe :
              -x l + (∑ i : Fin k, xParts i l) + ∑ j : Fin t, (μNat j : ℝ) * (r j l : ℝ) ≤ 0 := by
            linarith
          calc
            ((((intMatrix.map (Rat.castHom ℝ)) *ᵥ zReal) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x (flattenSelectorParts xParts)))
                (rowEquiv (SelectorConeLiftRow.xEqGe (n := n) (t := t) l)))
                =
              -x l + (∑ i : Fin k, xParts i l) + ∑ j : Fin t, (μNat j : ℝ) * (r j l : ℝ) := by
                  simpa [intMatrix, realMatrix, rowEquiv, z, zReal, hzRealEta, Matrix.mulVec, dotProduct,
                    add_comm, add_left_comm, add_assoc] using
                    (selectorConePackedXEqGeRow_eval (A := A) (b := b) (r := r) (x := x)
                      (xParts := xParts) (δ := fun i ↦ (δNat i : ℝ))
                      (μ := fun j ↦ (μNat j : ℝ)) l)
            _ ≤ 0 := hrowGe
            _ = (rhs (rowEquiv (SelectorConeLiftRow.xEqGe (n := n) (t := t) l)) : ℝ) := by
                  simp [rhs, rowEquiv, selectorConeLiftRhs]
      | selectorSumLe =>
          have hrowFin' :
              row = rowEquiv (SelectorConeLiftRow.selectorSumLe (n := n) (t := t)) := by
            calc
              row = rowEquiv (rowEquiv.symm row) := by
                symm
                exact Equiv.apply_symm_apply rowEquiv row
              _ = rowEquiv (SelectorConeLiftRow.selectorSumLe (n := n) (t := t)) := by
                    rw [hnative]
          rw [hrowFin']
          have hrowLe : ∑ i : Fin k, (δNat i : ℝ) ≤ 1 := by
            exact_mod_cast hδsum.le
          calc
            ((((intMatrix.map (Rat.castHom ℝ)) *ᵥ zReal) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x (flattenSelectorParts xParts)))
                (rowEquiv (SelectorConeLiftRow.selectorSumLe (n := n) (t := t))))
                = ∑ i : Fin k, (δNat i : ℝ) := by
                    simpa [intMatrix, realMatrix, rowEquiv, z, zReal, hzRealEta, Matrix.mulVec, dotProduct,
                      add_comm, add_left_comm, add_assoc] using
                      (selectorConePackedSelectorSumLeRow_eval (A := A) (b := b) (r := r) (x := x)
                        (xParts := xParts) (δ := fun i ↦ (δNat i : ℝ))
                        (μ := fun j ↦ (μNat j : ℝ)))
            _ ≤ 1 := hrowLe
            _ = (rhs (rowEquiv (SelectorConeLiftRow.selectorSumLe (n := n) (t := t))) : ℝ) := by
                  simp [rhs, rowEquiv, selectorConeLiftRhs]
      | selectorSumGe =>
          have hrowFin' :
              row = rowEquiv (SelectorConeLiftRow.selectorSumGe (n := n) (t := t)) := by
            calc
              row = rowEquiv (rowEquiv.symm row) := by
                symm
                exact Equiv.apply_symm_apply rowEquiv row
              _ = rowEquiv (SelectorConeLiftRow.selectorSumGe (n := n) (t := t)) := by
                    rw [hnative]
          rw [hrowFin']
          have hrowGe : -(∑ i : Fin k, (δNat i : ℝ)) ≤ -1 := by
            have hδsumReal : ∑ i : Fin k, (δNat i : ℝ) = 1 := by
              exact_mod_cast hδsum
            linarith
          calc
            ((((intMatrix.map (Rat.castHom ℝ)) *ᵥ zReal) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x (flattenSelectorParts xParts)))
                (rowEquiv (SelectorConeLiftRow.selectorSumGe (n := n) (t := t))))
                = -(∑ i : Fin k, (δNat i : ℝ)) := by
                    simpa [intMatrix, realMatrix, rowEquiv, z, zReal, hzRealEta, Matrix.mulVec, dotProduct,
                      add_comm, add_left_comm, add_assoc] using
                      (selectorConePackedSelectorSumGeRow_eval (A := A) (b := b) (r := r) (x := x)
                        (xParts := xParts) (δ := fun i ↦ (δNat i : ℝ))
                        (μ := fun j ↦ (μNat j : ℝ)))
            _ ≤ -1 := hrowGe
            _ = (rhs (rowEquiv (SelectorConeLiftRow.selectorSumGe (n := n) (t := t))) : ℝ) := by
                  simp [rhs, rowEquiv, selectorConeLiftRhs]
      | deltaNonneg i =>
          have hrowFin' :
              row = rowEquiv (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i) := by
            calc
              row = rowEquiv (rowEquiv.symm row) := by
                symm
                exact Equiv.apply_symm_apply rowEquiv row
              _ = rowEquiv (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i) := by
                    rw [hnative]
          rw [hrowFin']
          have hrowNonneg : -((δNat i : ℝ)) ≤ 0 := by
            exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le (δNat i))
          calc
            ((((intMatrix.map (Rat.castHom ℝ)) *ᵥ zReal) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x (flattenSelectorParts xParts)))
                (rowEquiv (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i)))
                = -((δNat i : ℝ)) := by
                    simpa [intMatrix, realMatrix, rowEquiv, z, zReal, hzRealEta, Matrix.mulVec, dotProduct,
                      add_comm, add_left_comm, add_assoc] using
                      (selectorConePackedDeltaNonnegRow_eval (A := A) (b := b) (r := r) (x := x)
                        (xParts := xParts) (δ := fun i ↦ (δNat i : ℝ))
                        (μ := fun j ↦ (μNat j : ℝ)) i)
            _ ≤ 0 := hrowNonneg
            _ = (rhs (rowEquiv (SelectorConeLiftRow.deltaNonneg (n := n) (t := t) i)) : ℝ) := by
                  simp [rhs, rowEquiv, selectorConeLiftRhs]
      | muNonneg j =>
          have hrowFin' :
              row = rowEquiv (SelectorConeLiftRow.muNonneg (n := n) (t := t) j) := by
            calc
              row = rowEquiv (rowEquiv.symm row) := by
                symm
                exact Equiv.apply_symm_apply rowEquiv row
              _ = rowEquiv (SelectorConeLiftRow.muNonneg (n := n) (t := t) j) := by
                    rw [hnative]
          rw [hrowFin']
          have hrowNonneg : -((μNat j : ℝ)) ≤ 0 := by
            exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le (μNat j))
          calc
            ((((intMatrix.map (Rat.castHom ℝ)) *ᵥ zReal) +
                ((realMatrix.map (Rat.castHom ℝ)) *ᵥ Fin.append x (flattenSelectorParts xParts)))
                (rowEquiv (SelectorConeLiftRow.muNonneg (n := n) (t := t) j)))
                = -((μNat j : ℝ)) := by
                    simpa [intMatrix, realMatrix, rowEquiv, z, zReal, hzRealEta, Matrix.mulVec, dotProduct,
                      add_comm, add_left_comm, add_assoc] using
                      (selectorConePackedMuNonnegRow_eval (A := A) (b := b) (r := r) (x := x)
                        (xParts := xParts) (δ := fun i ↦ (δNat i : ℝ))
                        (μ := fun j ↦ (μNat j : ℝ)) j)
            _ ≤ 0 := hrowNonneg
            _ = (rhs (rowEquiv (SelectorConeLiftRow.muNonneg (n := n) (t := t) j)) : ℝ) := by
                  simp [rhs, rowEquiv, selectorConeLiftRhs]
    refine ⟨flattenSelectorParts xParts, z, ?_⟩
    rw [selectorConeWitnessPolyhedron, mem_rational_mixed_polyhedron_iff]
    simpa [selectorConeWitnessIntMatrix, selectorConeWitnessRealMatrix, selectorConeWitnessRhs,
      selectorConeWitnessRowEquiv, rowEquiv, intMatrix, realMatrix, rhs] using hz

/-- Helper for Theorem 4.47: after flattening `ℤ^q × ℝ^(n+p)` into `ℝ^(q+n+p)`, the visible
`x`-projection drops both the leading integer block and the trailing auxiliary real block. -/
private def flattenedVisibleXProjection
    {n p q : ℕ} (u : Fin (q + (n + p)) → ℝ) : Fin n → ℝ :=
  fun l ↦ u (Fin.natAdd q (Fin.castAdd p l))

/-- Helper for Theorem 4.47: the flattened visible-`x` projection is a linear map. -/
private lemma isLinearMap_flattenedVisibleXProjection
    {n p q : ℕ} :
    IsLinearMap ℝ
      (flattenedVisibleXProjection : (Fin (q + (n + p)) → ℝ) → Fin n → ℝ) := by
  refine ⟨?_, ?_⟩
  · intro u v
    -- The visible coordinates are read coordinatewise from the flattened ambient vector.
    ext l
    simp [flattenedVisibleXProjection]
  · intro a u
    -- Scalar multiplication commutes with taking the visible coordinate block.
    ext l
    simp [flattenedVisibleXProjection]

/-- Helper for Theorem 4.47: projecting a rational polytope in the flattened mixed ambient space
to the visible `x` block preserves rational polyhedrality. -/
private lemma isRationalPolytope_image_flattenedVisibleXProjection
    {n p q : ℕ}
    {Q : Set (Fin (q + (n + p)) → ℝ)}
    (hQ : Q.IsRationalPolytope) :
    (flattenedVisibleXProjection '' Q).IsRationalPolytope := by
  rcases hQ with ⟨k, v, hv⟩
  refine ⟨k, fun i l ↦ v i (Fin.natAdd q (Fin.castAdd p l)), ?_⟩
  rw [hv]
  -- Push the visible-coordinate projection through the convex hull of the rational vertex family.
  have hlin : IsLinearMap ℝ
      (flattenedVisibleXProjection : (Fin (q + (n + p)) → ℝ) → Fin n → ℝ) :=
    isLinearMap_flattenedVisibleXProjection
  rw [hlin.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(fun j : Fin (q + (n + p)) ↦ (v i j : ℝ)), ⟨i, rfl⟩, rfl⟩

/-- Helper for Theorem 4.47: the canonical `mixed_integer_x_projection` is exactly the image of the
flattened mixed-integer points under `flattenedVisibleXProjection`. -/
private lemma flattenedVisibleXProjection_image_mixedIntegerPoints_eq
    {n p q : ℕ}
    (P : Set (MixedRealPoint q (n + p))) :
    flattenedVisibleXProjection '' (Fin.appendEquiv q (n + p) '' mixed_integer_points P) =
      mixed_integer_x_projection P := by
  ext x
  constructor
  · rintro ⟨u, ⟨wz, hwz, rfl⟩, rfl⟩
    -- Read the flattened witness back in mixed coordinates and keep only the visible `x` block.
    exact ⟨wz, hwz, by
      ext l
      simp [flattenedVisibleXProjection, Fin.appendEquiv]⟩
  · rintro ⟨wz, hwz, rfl⟩
    -- Flatten the mixed-space witness and observe that the visible coordinates are unchanged.
    refine ⟨Fin.appendEquiv q (n + p) wz, ⟨wz, hwz, rfl⟩, ?_⟩
    ext l
    simp [flattenedVisibleXProjection, Fin.appendEquiv]

/-- Helper for Theorem 4.47: projecting a flattened finite union plus one integral cone to the
visible `x` block preserves the finite union and drops the invisible coordinates of every ray. -/
private lemma flattenedVisibleXProjection_image_iUnion_add_integral_intcone_eq
    {n p q k t : ℕ}
    (Q : Fin k → Set (Fin (q + (n + p)) → ℝ))
    (r : Fin t → Fin (q + (n + p)) → ℤ) :
    flattenedVisibleXProjection '' ((⋃ i : Fin k, Q i) + integral_intcone r) =
      (⋃ i : Fin k, flattenedVisibleXProjection '' Q i) +
        integral_intcone
          (fun j : Fin t ↦ fun l : Fin n ↦ r j (Fin.natAdd q (Fin.castAdd p l))) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases Set.mem_add.1 hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    rcases Set.mem_iUnion.1 hu₁ with ⟨i, hui⟩
    rcases (mem_integral_intcone_iff).1 hu₂ with ⟨a, rfl⟩
    refine Set.mem_add.2 ⟨flattenedVisibleXProjection u₁, ?_, ?_, ?_, ?_⟩
    · -- The visible `x` block of the chosen piece stays in the projected finite union.
      exact Set.mem_iUnion.2 ⟨i, ⟨u₁, hui, rfl⟩⟩
    · exact ∑ j : Fin t, (a j : ℝ) •
        (fun l : Fin n ↦ (r j (Fin.natAdd q (Fin.castAdd p l)) : ℝ))
    · -- Projecting the cone combination simply projects each integral ray.
      exact (mem_integral_intcone_iff).2 ⟨a, rfl⟩
    · -- The visible coordinates distribute across the sum of the piece and cone parts.
      ext l
      simp [flattenedVisibleXProjection, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  · rintro ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    rcases Set.mem_iUnion.1 hx₁ with ⟨i, hxi⟩
    rcases hxi with ⟨u₁, hu₁, rfl⟩
    rcases (mem_integral_intcone_iff).1 hx₂ with ⟨a, rfl⟩
    let u₂ : Fin (q + (n + p)) → ℝ :=
      ∑ j : Fin t, (a j : ℝ) • (fun idx : Fin (q + (n + p)) ↦ (r j idx : ℝ))
    refine ⟨u₁ + u₂, Set.mem_add.2 ⟨u₁, Set.mem_iUnion.2 ⟨i, hu₁⟩, u₂, ?_, rfl⟩, ?_⟩
    · -- Reinflate the projected cone witness by restoring the dropped coordinates of each ray.
      exact (mem_integral_intcone_iff).2 ⟨a, rfl⟩
    · -- After reinflating the rays, taking the visible `x` block returns the prescribed sum.
      ext l
      simp [flattenedVisibleXProjection, u₂, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 4.47: once the mixed-integer points are decomposed on the flattened
ambient space, one final visible-`x` projection yields the desired union of rational pieces plus
the projected integral cone. -/
private lemma xProjection_transport_ofFlattenedDecomposition
    {n p q k t : ℕ}
    {P : Set (MixedRealPoint q (n + p))}
    {Q : Fin k → Set (Fin (q + (n + p)) → ℝ)}
    {r : Fin t → Fin (q + (n + p)) → ℤ}
    (hdecomp :
      Fin.appendEquiv q (n + p) '' mixed_integer_points P =
        (⋃ i : Fin k, Q i) + integral_intcone r) :
    mixed_integer_x_projection P =
      (⋃ i : Fin k, flattenedVisibleXProjection '' Q i) +
        integral_intcone
          (fun j : Fin t ↦ fun l : Fin n ↦ r j (Fin.natAdd q (Fin.castAdd p l))) := by
  -- Compare the canonical `mixed_integer_x_projection` to the same flattened witness surface,
  -- then project the finite union and cone in one step.
  calc
    mixed_integer_x_projection P =
        flattenedVisibleXProjection '' (Fin.appendEquiv q (n + p) '' mixed_integer_points P) := by
          symm
          exact flattenedVisibleXProjection_image_mixedIntegerPoints_eq P
    _ = flattenedVisibleXProjection '' ((⋃ i : Fin k, Q i) + integral_intcone r) := by
          rw [hdecomp]
    _ = (⋃ i : Fin k, flattenedVisibleXProjection '' Q i) +
          integral_intcone
            (fun j : Fin t ↦ fun l : Fin n ↦ r j (Fin.natAdd q (Fin.castAdd p l))) := by
          exact flattenedVisibleXProjection_image_iUnion_add_integral_intcone_eq Q r

/-- Helper for Theorem 4.47: a flattened ambient decomposition packages directly into the target
union-of-rational-polytopes-plus-integral-cone surface after projecting each flat piece to the
visible `x` block. -/
private lemma exists_unionRationalPolytopesAddIntegralIntcone_ofFlattenedDecomposition
    {n p q k t : ℕ}
    {P : Set (MixedRealPoint q (n + p))}
    {Q : Fin k → Set (Fin (q + (n + p)) → ℝ)}
    {r : Fin t → Fin (q + (n + p)) → ℤ}
    (hQ : ∀ i : Fin k, (Q i).IsRationalPolytope)
    (hdecomp :
      Fin.appendEquiv q (n + p) '' mixed_integer_points P =
        (⋃ i : Fin k, Q i) + integral_intcone r) :
    ∃ P' : Fin k → Set (Fin n → ℝ),
      (∀ i : Fin k, (P' i).IsRationalPolytope) ∧
        mixed_integer_x_projection P = (⋃ i : Fin k, P' i) +
          integral_intcone
            (fun j : Fin t ↦ fun l : Fin n ↦ r j (Fin.natAdd q (Fin.castAdd p l))) := by
  refine ⟨fun i ↦ flattenedVisibleXProjection '' Q i, ?_, ?_⟩
  · intro i
    -- Each projected flat piece stays rational polyhedral under the visible-coordinate map.
    exact isRationalPolytope_image_flattenedVisibleXProjection (hQ i)
  · -- The transport lemma already identifies the target `x`-projection with the projected
    -- flattened decomposition.
    exact xProjection_transport_ofFlattenedDecomposition hdecomp

/-- Helper for Theorem 4.47: once the flattened mixed-integer witness admits the Section 4.8
ambient decomposition, the target visible `x`-projection already has the required
union-of-rational-polytopes-plus-integral-cone form. -/
private lemma exists_unionRationalPolytopesAddIntegralIntcone_ofMixedIntegerWitness
    {n p q : ℕ}
    {P : Set (MixedRealPoint q (n + p))}
    (hflat :
      ∃ k t : ℕ,
        ∃ Q : Fin k → Set (Fin (q + (n + p)) → ℝ),
          ∃ r : Fin t → Fin (q + (n + p)) → ℤ,
            (∀ i : Fin k, (Q i).IsRationalPolytope) ∧
              Fin.appendEquiv q (n + p) '' mixed_integer_points P =
                (⋃ i : Fin k, Q i) + integral_intcone r) :
    ∃ k t : ℕ,
      ∃ P' : Fin k → Set (Fin n → ℝ),
        ∃ r' : Fin t → Fin n → ℤ,
          (∀ i : Fin k, (P' i).IsRationalPolytope) ∧
            mixed_integer_x_projection P = (⋃ i : Fin k, P' i) + integral_intcone r' := by
  rcases hflat with ⟨k, t, Q, r, hQ, hdecomp⟩
  -- Reuse the existing projection transport package and only rename the projected ray family.
  rcases exists_unionRationalPolytopesAddIntegralIntcone_ofFlattenedDecomposition
      hQ hdecomp with
    ⟨P', hP', hrepr⟩
  refine ⟨k, t, P', fun j l ↦ r j (Fin.natAdd q (Fin.castAdd p l)), hP', hrepr⟩

/-- Helper for Theorem 4.47: flattening by `Fin.appendEquiv` rewrites mixed-integer membership as
ambient flattened membership together with integrality of the first block. -/
private lemma memFlatMixedIntegerPoints_iff
    {n p : ℕ}
    {P : Set (MixedRealPoint n p)}
    {u : Fin (n + p) → ℝ} :
    u ∈ (Fin.appendEquiv n p '' mixed_integer_points P) ↔
      u ∈ (Fin.appendEquiv n p '' P) ∧
        (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    -- Unpack flattened mixed-integer membership into ambient membership and integrality
    -- of the first block.
    rcases (mem_mixed_integer_points_iff).1 hxy with ⟨hP, hxy_lattice⟩
    constructor
    · exact ⟨xy, hP, rfl⟩
    · rw [mem_mixed_integer_lattice_iff] at hxy_lattice
      simpa using hxy_lattice
  · rintro ⟨huP, huInt⟩
    rcases huP with ⟨xy, hxyP, rfl⟩
    -- The flattened integrality condition is exactly the mixed-lattice condition on `xy`.
    refine ⟨xy, ?_, rfl⟩
    refine (mem_mixed_integer_points_iff).2 ⟨hxyP, ?_⟩
    rw [mem_mixed_integer_lattice_iff]
    simpa using huInt

/-- Helper for Theorem 4.47: the flattened points whose first `n` coordinates are integral. -/
private def firstBlockIntegerSet
    {n p : ℕ} : Set (Fin (n + p) → ℝ) :=
  {u | (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n}

/-- Helper for Theorem 4.47: the sum of two integer vectors is again an integer vector. -/
private lemma integerVectors_add_mem
    {n : ℕ}
    {u v : Fin n → ℝ}
    (hu : u ∈ integerVectors n)
    (hv : v ∈ integerVectors n) :
    u + v ∈ integerVectors n := by
  rcases (mem_integerVectors_iff).1 hu with ⟨a, rfl⟩
  rcases (mem_integerVectors_iff).1 hv with ⟨b, rfl⟩
  -- Add the underlying integer witnesses coordinatewise before casting back to `ℝ`.
  refine (mem_integerVectors_iff).2 ⟨fun i ↦ a i + b i, ?_⟩
  funext i
  simp

/-- Helper for Theorem 4.47: subtracting one integer vector from another keeps the result in the
integer lattice. -/
private lemma integerVectors_sub_mem
    {n : ℕ}
    {u v : Fin n → ℝ}
    (hu : u ∈ integerVectors n)
    (hv : v ∈ integerVectors n) :
    u - v ∈ integerVectors n := by
  rcases (mem_integerVectors_iff).1 hu with ⟨a, rfl⟩
  rcases (mem_integerVectors_iff).1 hv with ⟨b, rfl⟩
  -- Subtract the integer witnesses coordinatewise before casting to the ambient real space.
  refine (mem_integerVectors_iff).2 ⟨fun i ↦ a i - b i, ?_⟩
  funext i
  simp

/-- Helper for Theorem 4.47: every element of `integral_intcone r` has integral first block after
flattening. -/
private lemma firstBlock_mem_integerVectors_of_mem_integralIntcone
    {n p q : ℕ}
    {r : Fin q → Fin (n + p) → ℤ}
    {u : Fin (n + p) → ℝ}
    (hu : u ∈ integral_intcone r) :
    (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
  rcases (mem_integral_intcone_iff).1 hu with ⟨a, rfl⟩
  -- The first block is a finite integer linear combination of the integral ray coordinates.
  refine (mem_integerVectors_iff).2 ⟨fun i ↦ ∑ j : Fin q, (a j : ℤ) * r j (Fin.castAdd p i), ?_⟩
  funext i
  simp [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 4.47: once the flattened ambient set is in the normal form
`Q + integral_intcone r`, the flattened mixed-integer points are exactly the integer slice of `Q`
translated by the same integral cone. -/
private lemma flatMixedIntegerPoints_eq_baseSlice_add_integralIntcone
    {n p q : ℕ}
    {P : Set (MixedRealPoint n p)}
    {Q : Set (Fin (n + p) → ℝ)}
    {r : Fin q → Fin (n + p) → ℤ}
    (hdecomp : Fin.appendEquiv n p '' P = Q + integral_intcone r) :
    Fin.appendEquiv n p '' mixed_integer_points P =
      (Q ∩ firstBlockIntegerSet) + integral_intcone r := by
  ext u
  constructor
  · intro hu
    rcases (memFlatMixedIntegerPoints_iff).1 hu with ⟨huP, huInt⟩
    rw [hdecomp] at huP
    rcases Set.mem_add.1 huP with ⟨q, hqQ, c, hc, rfl⟩
    refine Set.mem_add.2 ⟨q, ?_, c, hc, rfl⟩
    refine ⟨hqQ, ?_⟩
    have hqcInt :
        (fun i : Fin n ↦ (q + c) (Fin.castAdd p i)) ∈ integerVectors n := by
      simpa [firstBlockIntegerSet] using huInt
    have hcInt :
        (fun i : Fin n ↦ c (Fin.castAdd p i)) ∈ integerVectors n :=
      firstBlock_mem_integerVectors_of_mem_integralIntcone hc
    -- Subtract the integral cone contribution to recover an integral first block for `q`.
    have hqEq :
        (fun i : Fin n ↦ q (Fin.castAdd p i)) =
          (fun i : Fin n ↦ (q + c) (Fin.castAdd p i)) -
            fun i : Fin n ↦ c (Fin.castAdd p i) := by
      funext i
      simp [Pi.sub_apply]
    have hqInt :
        (fun i : Fin n ↦ q (Fin.castAdd p i)) ∈ integerVectors n := by
      rw [hqEq]
      exact integerVectors_sub_mem hqcInt hcInt
    simpa [firstBlockIntegerSet] using hqInt
  · intro hu
    rcases Set.mem_add.1 hu with ⟨q, hq, c, hc, rfl⟩
    rcases hq with ⟨hqQ, hqInt⟩
    refine (memFlatMixedIntegerPoints_iff).2 ?_
    refine ⟨?_, ?_⟩
    · rw [hdecomp]
      exact Set.mem_add.2 ⟨q, hqQ, c, hc, rfl⟩
    · have hcInt :
          (fun i : Fin n ↦ c (Fin.castAdd p i)) ∈ integerVectors n :=
        firstBlock_mem_integerVectors_of_mem_integralIntcone hc
      have hqInt' :
          (fun i : Fin n ↦ q (Fin.castAdd p i)) ∈ integerVectors n := by
        simpa [firstBlockIntegerSet] using hqInt
      -- Add the integral cone contribution back to the integer slice of `Q`.
      simpa [Pi.add_apply] using integerVectors_add_mem hqInt' hcInt

/-- Helper for Theorem 4.47: a rational polytope has a uniform integer bound on its first block.
-/
private lemma boundedFirstBlockCoordinates_of_isRationalPolytope
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : Q.IsRationalPolytope) :
    ∃ B : ℤ,
      ∀ ⦃u : Fin (n + p) → ℝ⦄, u ∈ Q → ∀ i : Fin n,
        (-(B : ℝ)) ≤ u (Fin.castAdd p i) ∧ u (Fin.castAdd p i) ≤ (B : ℝ) := by
  rcases (Set.IsRationalPolytope.isPolytope hQ) with ⟨V, hVfinite, hVeq⟩
  have hQ_bounded : Bornology.IsBounded Q := by
    -- Rational polytopes are bounded because they are finite convex hulls.
    simpa [hVeq] using (isBounded_convexHull).2 hVfinite.isBounded
  obtain ⟨R, hR⟩ := hQ_bounded.subset_closedBall (0 : Fin (n + p) → ℝ)
  let B : ℤ := Int.ceil (max R 0)
  refine ⟨B, ?_⟩
  intro u hu i
  have hu_ball : u ∈ Metric.closedBall (0 : Fin (n + p) → ℝ) R := hR hu
  have hu_norm : ‖u‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
  have hcoord_norm : ‖u (Fin.castAdd p i)‖ ≤ ‖u‖ := norm_le_pi_norm u (Fin.castAdd p i)
  have hcoord_abs : |u (Fin.castAdd p i)| ≤ max R 0 := by
    -- Coordinate norms are controlled by the ambient norm, which is controlled by the ball radius.
    calc
      |u (Fin.castAdd p i)| = ‖u (Fin.castAdd p i)‖ := by simp
      _ ≤ ‖u‖ := hcoord_norm
      _ ≤ R := hu_norm
      _ ≤ max R 0 := le_max_left _ _
  have hB_ge : max R 0 ≤ (B : ℝ) := Int.le_ceil (max R 0)
  exact abs_le.mp (hcoord_abs.trans hB_ge)

/-- Helper for Theorem 4.47: fixing the first `n` coordinates to one integer vector defines the
corresponding coordinate fiber. -/
private def firstBlockFiber
    {n p : ℕ}
    (z : Fin n → ℤ) : Set (Fin (n + p) → ℝ) :=
  {u | (fun i : Fin n ↦ u (Fin.castAdd p i)) = Int.cast ∘ z}

/-- Helper for Theorem 4.47: a bounded nonempty set has no nonzero recession direction. -/
private lemma recessionCone_eq_singleton_zero_of_nonempty_bounded
    {k : ℕ}
    {P : Set (Fin k → ℝ)}
    (hP_nonempty : P.Nonempty)
    (hP_bounded : Bornology.IsBounded P) :
    recessionCone P = ({0} : Set (Fin k → ℝ)) := by
  obtain ⟨x₀, hx₀⟩ := hP_nonempty
  have htranslate :
      ({x₀} + recessionCone P) ⊆ P := by
    -- Translate any recession direction by one feasible base point to stay inside `P`.
    rintro y ⟨x', hx', r, hr, rfl⟩
    rw [Set.mem_singleton_iff] at hx'
    subst x'
    rw [mem_recessionCone_iff] at hr
    simpa using hr hx₀ 1 zero_le_one
  have hrec_bounded : Bornology.IsBounded (recessionCone P) := by
    -- The translated recession cone sits inside the bounded ambient set `P`.
    obtain ⟨R, _, hP_ball⟩ := hP_bounded.subset_ball_lt 0 (0 : Fin k → ℝ)
    exact Bornology.IsBounded.subset
      (show Bornology.IsBounded (Metric.ball (0 : Fin k → ℝ) (R + ‖x₀‖)) from
        Metric.isBounded_ball)
      (by
        intro r hr
        have hxrP : x₀ + r ∈ P := by
          exact htranslate ⟨x₀, Set.mem_singleton x₀, r, hr, by simp⟩
        have hxr_ball : ‖x₀ + r‖ < R := by
          simpa [Metric.mem_ball, dist_eq_norm] using hP_ball hxrP
        have hr_eq : r = (x₀ + r) + (-x₀) := by
          ext i
          simp
        have hr_norm_le : ‖r‖ ≤ ‖x₀ + r‖ + ‖x₀‖ := by
          rw [hr_eq]
          simpa using norm_add_le (x₀ + r) (-x₀)
        have hr_norm_lt : ‖r‖ < R + ‖x₀‖ := by
          linarith
        simpa [Metric.mem_ball, dist_eq_norm] using hr_norm_lt)
  ext r
  constructor
  · intro hr
    by_cases hr0 : r = 0
    · simp [hr0]
    · obtain ⟨R, hR⟩ := hrec_bounded.subset_closedBall (0 : Fin k → ℝ)
      have hzero_mem : (0 : Fin k → ℝ) ∈ recessionCone P := zero_mem_recessionCone
      have hR_nonneg : 0 ≤ R := by
        have hzero_ball : (0 : Fin k → ℝ) ∈ Metric.closedBall (0 : Fin k → ℝ) R := hR hzero_mem
        simpa [Metric.mem_closedBall] using hzero_ball
      have hr_norm_pos : 0 < ‖r‖ := norm_pos_iff.mpr hr0
      have hr_norm_ne : ‖r‖ ≠ 0 := ne_of_gt hr_norm_pos
      have ht_nonneg : 0 ≤ R / ‖r‖ + 1 := by positivity
      have htr_mem : ((R / ‖r‖ + 1) • r) ∈ recessionCone P :=
        smul_mem_recessionCone hr ht_nonneg
      have hmem_ball :
          ((R / ‖r‖ + 1) • r) ∈ Metric.closedBall (0 : Fin k → ℝ) R := hR htr_mem
      have htr_bound : ‖(R / ‖r‖ + 1) • r‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hmem_ball
      have htr_norm : ‖(R / ‖r‖ + 1) • r‖ = R + ‖r‖ := by
        calc
          ‖(R / ‖r‖ + 1) • r‖ = |R / ‖r‖ + 1| * ‖r‖ := norm_smul _ _
          _ = (R / ‖r‖ + 1) * ‖r‖ := by rw [abs_of_nonneg ht_nonneg]
          _ = (R / ‖r‖) * ‖r‖ + ‖r‖ := by rw [add_mul, one_mul]
          _ = R + ‖r‖ := by rw [div_mul_cancel₀ _ hr_norm_ne]
      have hlarge : R + ‖r‖ ≤ R := by
        simpa [htr_norm] using htr_bound
      linarith
  · intro hr
    have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
    subst hr0
    exact zero_mem_recessionCone

/-- Helper for Theorem 4.47: a nonempty bounded rational matrix polyhedron is a rational
polytope. -/
private lemma rationalMatrixPolyhedron_isRationalPolytope_of_nonempty_bounded
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {b : Fin m → ℚ}
    (hP_nonempty : (rational_matrix_polyhedron A b).Nonempty)
    (hP_bounded : Bornology.IsBounded (rational_matrix_polyhedron A b)) :
    (rational_matrix_polyhedron A b).IsRationalPolytope := by
  classical
  let P : Set (Fin n → ℝ) := rational_matrix_polyhedron A b
  have hP_polyhedron : is_polyhedron P := by
    -- Re-express the rational system as an ordinary real polyhedron.
    refine (is_polyhedron_iff).2 ?_
    exact ⟨m, A.map (Rat.castHom ℝ), fun i ↦ (b i : ℝ), rfl⟩
  rcases (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).1 hP_polyhedron with
    ⟨Q, hQ_polytope, q, rays, hP_repr⟩
  rcases hQ_polytope with ⟨V, hV_finite, hQ_eq⟩
  have hQ_polytope' : Q.IsPolytope ℝ := ⟨V, hV_finite, hQ_eq⟩
  obtain ⟨p, vertex, -, hV_range⟩ := hV_finite.fin_param
  have hP_rec_zero : recessionCone P = ({0} : Set (Fin n → ℝ)) :=
    recessionCone_eq_singleton_zero_of_nonempty_bounded hP_nonempty hP_bounded
  have hP_rec_rays :
      recessionCone P = finitely_generated_cone rays := by
    -- Route correction: compute the recession cone from the `polytope + cone` normal form first,
    -- then collapse the cone using boundedness instead of importing the Section 4.8 helper.
    have hP_repr' :
        P = convexHull ℝ (Set.range vertex) + finitely_generated_cone rays := by
      calc
        P = Q + finitely_generated_cone rays := hP_repr
        _ = convexHull ℝ V + finitely_generated_cone rays := by rw [hQ_eq]
        _ = convexHull ℝ (Set.range vertex) + finitely_generated_cone rays := by rw [hV_range]
    exact
      polyhedron_recessionCone_eq_finitely_generated_cone
        (A := A.map (Rat.castHom ℝ))
        (b := fun i ↦ (b i : ℝ))
        vertex
        rays
        hP_nonempty
        (by simpa [P] using hP_repr')
  have hcone_zero : finitely_generated_cone rays = ({0} : Set (Fin n → ℝ)) := by
    calc
      finitely_generated_cone rays = recessionCone P := hP_rec_rays.symm
      _ = ({0} : Set (Fin n → ℝ)) := hP_rec_zero
  have hP_eq_Q : P = Q := by
    -- Once the recession cone vanishes, the polyhedron is exactly its bounded polytope part.
    calc
      P = Q + finitely_generated_cone rays := hP_repr
      _ = Q + ({0} : Set (Fin n → ℝ)) := by rw [hcone_zero]
      _ = Q := by
            ext x
            constructor
            · intro hx
              rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, hsum⟩
              have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
              have hyx : y = x := by simpa [hz0] using hsum
              simpa [hyx] using hy
            · intro hx
              exact Set.mem_add.mpr ⟨x, hx, 0, Set.mem_singleton 0, by simp⟩
  have hP_polytope : P.IsPolytope ℝ := by
    simpa [hP_eq_Q] using hQ_polytope'
  rcases hP_polytope with ⟨Vpoly, hVpoly_finite, hP_hull⟩
  have hP_compact : IsCompact P := by
    -- A polytope is compact because it is the convex hull of finitely many points.
    rw [hP_hull]
    exact hVpoly_finite.isCompact_convexHull ℝ
  have hP_convex : Convex ℝ P := by
    rw [hP_hull]
    exact convex_convexHull ℝ Vpoly
  have hPext_subset :
      P.extremePoints ℝ ⊆ Vpoly := by
    intro x hx
    rw [hP_hull] at hx
    exact extremePoints_convexHull_subset hx
  have hPext_finite : (P.extremePoints ℝ).Finite :=
    hVpoly_finite.subset hPext_subset
  have hP_eq_convexHull_extreme :
      P = convexHull ℝ (P.extremePoints ℝ) := by
    have hclosure := closure_convexHull_extremePoints hP_compact hP_convex
    calc
      P = closure (convexHull ℝ (P.extremePoints ℝ)) := by
            simpa using hclosure.symm
      _ = convexHull ℝ (P.extremePoints ℝ) := by
            exact (hPext_finite.isClosed_convexHull ℝ).closure_eq
  obtain ⟨t, xext, -, hxext_range⟩ := hPext_finite.fin_param
  let L : ℕ :=
    (∑ i : Fin m, ∑ j : Fin n, EncodingSize.rational (A i j)) +
      ∑ i : Fin m, EncodingSize.rational (b i)
  have hA_bound : ∀ i j, EncodingSize.rational (A i j) ≤ L := by
    intro i j
    have hij :
        EncodingSize.rational (A i j) ≤
          ∑ j' : Fin n, EncodingSize.rational (A i j') := by
      exact Finset.single_le_sum
        (fun j' _ ↦ Nat.zero_le (EncodingSize.rational (A i j')))
        (Finset.mem_univ j)
    have hii :
        ∑ j' : Fin n, EncodingSize.rational (A i j') ≤
          ∑ i' : Fin m, ∑ j' : Fin n, EncodingSize.rational (A i' j') := by
      exact Finset.single_le_sum
        (fun i' _ ↦ Nat.zero_le (∑ j' : Fin n, EncodingSize.rational (A i' j')))
        (Finset.mem_univ i)
    calc
      EncodingSize.rational (A i j) ≤
          ∑ j' : Fin n, EncodingSize.rational (A i j') := hij
      _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, EncodingSize.rational (A i' j') := hii
      _ ≤ L := Nat.le.intro rfl
  have hb_bound : ∀ i : Fin m, EncodingSize.rational (b i) ≤ L := by
    intro i
    have hi :
        EncodingSize.rational (b i) ≤
          ∑ i' : Fin m, EncodingSize.rational (b i') := by
      exact Finset.single_le_sum
        (fun i' _ ↦ Nat.zero_le (EncodingSize.rational (b i')))
        (Finset.mem_univ i)
    calc
      EncodingSize.rational (b i) ≤ ∑ i' : Fin m, EncodingSize.rational (b i') := hi
      _ ≤ L := Nat.le_add_left _ _
  obtain ⟨π, hπ⟩ := rational_vertices_have_polynomially_bounded_encoding_size
  choose vertexQ hvertexQ_eq hvertexQ_bound using
    fun i : Fin t ↦ by
      have hxext_mem : xext i ∈ P.extremePoints ℝ := by
        rw [← hxext_range]
        exact Set.mem_range_self i
      exact hπ A b L hA_bound hb_bound (xext i) hxext_mem
  refine ⟨t, vertexQ, ?_⟩
  have hvertexQ_range :
      Set.range (fun i : Fin t ↦ fun j : Fin n ↦ (vertexQ i j : ℝ)) = P.extremePoints ℝ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [← hxext_range]
      exact ⟨i, hvertexQ_eq i⟩
    · intro hx
      rw [← hxext_range] at hx
      rcases hx with ⟨i, rfl⟩
      exact ⟨i, (hvertexQ_eq i).symm⟩
  -- Replace the compact convex polyhedron by the convex hull of its rational extreme points.
  calc
    P = convexHull ℝ (P.extremePoints ℝ) := hP_eq_convexHull_extreme
    _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun j : Fin n ↦ (vertexQ i j : ℝ)) := by
          rw [← hvertexQ_range]

/-- Helper for Theorem 4.47: a selector row supported on the first block recovers the chosen
coordinate. -/
private lemma sumFirstBlockSelectorRow_eq_active
    {n p : ℕ}
    (u : Fin (n + p) → ℝ)
    (i : Fin n)
    (c : ℚ) :
    ∑ j : Fin (n + p),
        (((Fin.append
            (fun l : Fin n ↦ if l = i then c else 0)
            (fun _ : Fin p ↦ 0) j : ℚ) : ℝ) * u j) =
      (c : ℝ) * u (Fin.castAdd p i) := by
  -- Split the flattened coordinates into the first block and the tail block before collapsing
  -- the singleton selector.
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, zero_mul, Finset.sum_const_zero, add_zero]
  simpa using sumCastIteMul_eq_active (fun l : Fin n ↦ u (Fin.castAdd p l)) i c

/-- Helper for Theorem 4.47: augmenting a rational matrix presentation by paired `±Id` rows on
the first block cuts out the fixed-first-block fiber. -/
private lemma firstBlockFiberAugmentedRhs_lower_apply
    {n m : ℕ}
    (b : Fin m → ℚ)
    (z : Fin n → ℤ)
    (i : Fin n) :
    ((Fin.addCases b
        (Fin.addCases (fun i' : Fin n ↦ (z i' : ℚ)) (fun i' : Fin n ↦ -(z i' : ℚ)))
        (Fin.natAdd m (Fin.natAdd n i)) : ℚ) : ℝ) =
      -(z i : ℝ) := by
  -- The lower augmented row sits in the negative copy of the first-block equality system.
  change
    (((Fin.addCases b
        (Fin.addCases (fun i' ↦ (z i' : ℚ)) (fun i' ↦ -(z i' : ℚ)))
        (Fin.natAdd m (Fin.natAdd n i)) : ℚ) : ℝ)) =
      -(z i : ℝ)
  rw [Fin.addCases_right]
  show
    (((Fin.addCases (fun i' ↦ (z i' : ℚ)) (fun i' ↦ -(z i' : ℚ))
        (Fin.natAdd n i) : ℚ) : ℝ)) =
      -(z i : ℝ)
  rw [Fin.addCases_right]
  simp

/-- Helper for Theorem 4.47: augmenting a rational matrix presentation by paired `±Id` rows on
the first block cuts out the fixed-first-block fiber. -/
private lemma firstBlockFiber_eq_rationalMatrixPolyhedron
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : Q.IsRationalPolytope)
    (z : Fin n → ℤ) :
    ∃ m : ℕ,
      ∃ A : Matrix (Fin m) (Fin (n + p)) ℚ,
        ∃ b : Fin m → ℚ,
          Q ∩ firstBlockFiber z = rational_matrix_polyhedron A b := by
  rcases rationalPolytope_eq_rationalMatrixPolyhedron hQ with ⟨m, A, b, hQeq⟩
  let A' : Matrix (Fin (m + (n + n))) (Fin (n + p)) ℚ :=
    fun i ↦
      Fin.addCases
        A
        (Fin.addCases
          (fun i' ↦ Fin.append (fun j ↦ if j = i' then 1 else 0) (fun _ ↦ 0))
          (fun i' ↦ Fin.append (fun j ↦ if j = i' then -1 else 0) (fun _ ↦ 0)))
        i
  let b' : Fin (m + (n + n)) → ℚ :=
    fun i ↦
      Fin.addCases
        b
        (Fin.addCases
          (fun i' ↦ z i')
          (fun i' ↦ -(z i')))
        i
  refine ⟨m + (n + n), A', b', ?_⟩
  ext u
  constructor
  · intro hu
    rcases hu with ⟨huQ, huFiber⟩
    rw [hQeq, mem_rational_matrix_polyhedron] at huQ
    rw [mem_rational_matrix_polyhedron]
    intro row
    refine Fin.addCases ?_ ?_ row
    · intro s
      have hrow :
          (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.castAdd (n + n) s)) =
            (((A.map (Rat.castHom ℝ)) *ᵥ u) s) := by
        simp [A', Matrix.mulVec, dotProduct]
      rw [hrow]
      simpa [hQeq, b'] using huQ s
    · intro row'
      refine Fin.addCases ?_ ?_ row'
      · intro i
        have hi : u (Fin.castAdd p i) = (z i : ℝ) := by
          simpa [firstBlockFiber, Function.comp] using congrFun huFiber i
        have hrow :
            (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.natAdd m (Fin.castAdd n i))) =
              u (Fin.castAdd p i) := by
          simpa [A', Matrix.mulVec, dotProduct, Fin.sum_univ_add] using
            sumFirstBlockSelectorRow_eq_active u i 1
        rw [hrow]
        simpa [b', hi]
      · intro i
        have hi : u (Fin.castAdd p i) = (z i : ℝ) := by
          simpa [firstBlockFiber, Function.comp] using congrFun huFiber i
        have hrow :
            (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.natAdd m (Fin.natAdd n i))) =
              (-1 : ℝ) * u (Fin.castAdd p i) := by
          have hcoeffLeft :
              ∀ j : Fin n,
                (((A'.map (Rat.castHom ℝ)) (Fin.natAdd m (Fin.natAdd n i)) (Fin.castAdd p j)) : ℝ) =
                  if j = i then (-1 : ℝ) else 0 := by
            intro j
            have hnat : i.addNat n = Fin.natAdd n i := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [A']
            rw [hnat, Fin.addCases_right]
            by_cases h : j = i <;> simp [h]
          have hcoeffRight :
              ∀ j : Fin p,
                (((A'.map (Rat.castHom ℝ)) (Fin.natAdd m (Fin.natAdd n i)) (Fin.natAdd n j)) : ℝ) =
                  0 := by
            intro j
            have hnat : i.addNat n = Fin.natAdd n i := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [A']
            rw [hnat, Fin.addCases_right]
            simp
          rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
          simp_rw [hcoeffLeft, hcoeffRight]
          simpa using sumCastIteMul_eq_active (fun l : Fin n ↦ u (Fin.castAdd p l)) i (-1)
        rw [hrow]
        have hb :
            (b' (Fin.natAdd m (Fin.natAdd n i)) : ℝ) = -(z i : ℝ) := by
          simpa [b'] using firstBlockFiberAugmentedRhs_lower_apply (b := b) z i
        change (-1 : ℝ) * u (Fin.castAdd p i) ≤ (b' (Fin.natAdd m (Fin.natAdd n i)) : ℝ)
        rw [hb, hi]
        simp
  · intro hu
    rw [mem_rational_matrix_polyhedron] at hu
    refine ⟨?_, ?_⟩
    · rw [hQeq, mem_rational_matrix_polyhedron]
      intro s
      have hrow :
          (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.castAdd (n + n) s)) =
            (((A.map (Rat.castHom ℝ)) *ᵥ u) s) := by
        simp [A', Matrix.mulVec, dotProduct]
      rw [← hrow]
      simpa [b'] using hu (Fin.castAdd (n + n) s)
    · ext i
      have hupper := hu (Fin.natAdd m (Fin.castAdd n i))
      have hlower := hu (Fin.natAdd m (Fin.natAdd n i))
      have hupper' : u (Fin.castAdd p i) ≤ (z i : ℝ) := by
        have hrow :
            (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.natAdd m (Fin.castAdd n i))) =
              u (Fin.castAdd p i) := by
          simpa [A', Matrix.mulVec, dotProduct, Fin.sum_univ_add] using
            sumFirstBlockSelectorRow_eq_active u i 1
        rw [hrow] at hupper
        simpa [b'] using hupper
      have hlower' : (-1 : ℝ) * u (Fin.castAdd p i) ≤ -(z i : ℝ) := by
        have hrow :
            (((A'.map (Rat.castHom ℝ)) *ᵥ u) (Fin.natAdd m (Fin.natAdd n i))) =
              (-1 : ℝ) * u (Fin.castAdd p i) := by
          have hcoeffLeft :
              ∀ j : Fin n,
                (((A'.map (Rat.castHom ℝ)) (Fin.natAdd m (Fin.natAdd n i)) (Fin.castAdd p j)) : ℝ) =
                  if j = i then (-1 : ℝ) else 0 := by
            intro j
            have hnat : i.addNat n = Fin.natAdd n i := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [A']
            rw [hnat, Fin.addCases_right]
            by_cases h : j = i <;> simp [h]
          have hcoeffRight :
              ∀ j : Fin p,
                (((A'.map (Rat.castHom ℝ)) (Fin.natAdd m (Fin.natAdd n i)) (Fin.natAdd n j)) : ℝ) =
                  0 := by
            intro j
            have hnat : i.addNat n = Fin.natAdd n i := by
              apply Fin.ext
              simpa [Nat.add_comm] using rfl
            simp [A']
            rw [hnat, Fin.addCases_right]
            simp
          rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
          simp_rw [hcoeffLeft, hcoeffRight]
          simpa using sumCastIteMul_eq_active (fun l : Fin n ↦ u (Fin.castAdd p l)) i (-1)
        rw [hrow] at hlower
        have hb :
            (b' (Fin.natAdd m (Fin.natAdd n i)) : ℝ) = -(z i : ℝ) := by
          simpa [b'] using firstBlockFiberAugmentedRhs_lower_apply (b := b) z i
        change (-1 : ℝ) * u (Fin.castAdd p i) ≤ (b' (Fin.natAdd m (Fin.natAdd n i)) : ℝ) at hlower
        rw [hb] at hlower
        simpa using hlower
      have hlower'' : (z i : ℝ) ≤ u (Fin.castAdd p i) := by
        linarith
      exact le_antisymm hupper' hlower''

/-- Helper for Theorem 4.47: every fixed-first-block fiber of a rational polytope is again a
rational polytope. -/
private lemma firstBlockFiber_isRationalPolytope
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : Q.IsRationalPolytope)
    (z : Fin n → ℤ) :
    (Q ∩ firstBlockFiber z).IsRationalPolytope := by
  classical
  by_cases hFiber_nonempty : (Q ∩ firstBlockFiber z).Nonempty
  · rcases firstBlockFiber_eq_rationalMatrixPolyhedron hQ z with ⟨m, A, b, hFiber_eq⟩
    have hQ_bounded : Bornology.IsBounded Q := by
      -- Rational polytopes are bounded because they are finite convex hulls.
      rcases (Set.IsRationalPolytope.isPolytope hQ) with ⟨V, hV, hVeq⟩
      simpa [hVeq] using (isBounded_convexHull).2 hV.isBounded
    have hFiber_bounded : Bornology.IsBounded (Q ∩ firstBlockFiber z) := by
      exact hQ_bounded.subset (by
        intro u hu
        exact hu.1)
    -- Route correction: for a fixed first-block fiber, boundedness already kills the recession
    -- cone, so we can prove rational polyhedrality directly and avoid the imported Section 4.8
    -- compatible-vertex theorem.
    have hFiber_nonempty_matrix : (rational_matrix_polyhedron A b).Nonempty := by
      rw [← hFiber_eq]
      exact hFiber_nonempty
    have hFiber_bounded_matrix : Bornology.IsBounded (rational_matrix_polyhedron A b) := by
      rw [← hFiber_eq]
      exact hFiber_bounded
    simpa [hFiber_eq] using
      rationalMatrixPolyhedron_isRationalPolytope_of_nonempty_bounded
        hFiber_nonempty_matrix
        hFiber_bounded_matrix
  · have hFiber_empty : Q ∩ firstBlockFiber z = ∅ := Set.not_nonempty_iff_eq_empty.mp hFiber_nonempty
    -- The empty fiber is the convex hull of the empty rational vertex family.
    refine ⟨0, Fin.elim0, ?_⟩
    simpa [hFiber_empty]

/-- Helper for Theorem 4.47: the integer slice of one rational polytope is a finite union of
fixed-first-block rational-polytopal fibers. -/
private lemma existsRationalPolytopeFirstBlockIntegerSlices
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : Q.IsRationalPolytope) :
    ∃ K : ℕ,
      ∃ Qs : Fin K → Set (Fin (n + p) → ℝ),
        (∀ j : Fin K, (Qs j).IsRationalPolytope) ∧
          (Q ∩ firstBlockIntegerSet = ⋃ j : Fin K, Qs j) := by
  classical
  obtain ⟨B, hB⟩ := boundedFirstBlockCoordinates_of_isRationalPolytope hQ
  let box : Set (Fin n → ℤ) := {ρ | ∀ i : Fin n, ρ i ∈ Set.Icc (-B) B}
  have hboxFinite : box.Finite := by
    -- Enumerate all bounded integer first blocks coordinatewise.
    simpa [box, Set.pi] using
      (Set.Finite.pi' (t := fun i : Fin n ↦ Set.Icc (-B) B)
        fun i ↦ Set.finite_Icc (-B) B)
  obtain ⟨K, z, hz_inj, hz_range⟩ := hboxFinite.fin_param
  let Qs : Fin K → Set (Fin (n + p) → ℝ) := fun j ↦ Q ∩ firstBlockFiber (z j)
  refine ⟨K, Qs, ?_, ?_⟩
  · intro j
    -- Each enumerated first-block slice is a rational polytope.
    exact firstBlockFiber_isRationalPolytope hQ (z j)
  · -- Route correction: enumerate bounded integer first blocks of one piece and only then
    -- aggregate across the outer family.
    ext u
    constructor
    · intro hu
      rcases hu with ⟨huQ, huInt⟩
      have huInt' : (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
        simpa [firstBlockIntegerSet] using huInt
      rcases (mem_integerVectors_iff).1 huInt' with ⟨ρ, hρ⟩
      have hρ_box : ∀ i : Fin n, ρ i ∈ Set.Icc (-B) B := by
        intro i
        have hcoord := hB huQ i
        have hcoordEq : u (Fin.castAdd p i) = (ρ i : ℝ) := by
          simpa [Function.comp] using congrFun hρ i
        constructor
        · have hlow : (-(B : ℝ)) ≤ (ρ i : ℝ) := by
            simpa [hcoordEq] using hcoord.1
          exact_mod_cast hlow
        · have hupp : (ρ i : ℝ) ≤ (B : ℝ) := by
            simpa [hcoordEq] using hcoord.2
          exact_mod_cast hupp
      have hρ_mem : ρ ∈ box := hρ_box
      rw [← hz_range] at hρ_mem
      rcases hρ_mem with ⟨j, hj⟩
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      refine ⟨huQ, ?_⟩
      simpa [Qs, firstBlockFiber, Function.comp, hj] using hρ
    · intro hu
      rcases Set.mem_iUnion.1 hu with ⟨j, huj⟩
      rcases huj with ⟨huQ, huFiber⟩
      refine ⟨huQ, ?_⟩
      have huInt :
          (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
        refine (mem_integerVectors_iff).2 ⟨z j, ?_⟩
        simpa [Qs, firstBlockFiber, Function.comp] using huFiber
      simpa [firstBlockIntegerSet] using huInt

/-- Helper for Theorem 4.47: after the ambient decomposition is fixed, the bounded integer slice
of a finite rational-polytope family should itself be replaced by one finite rational-polytope
family. -/
private lemma existsFamilyRationalPolytopeFirstBlockIntegerSlices
    {n p k : ℕ}
    {Q : Fin k → Set (Fin (n + p) → ℝ)}
    (hQ : ∀ i : Fin k, (Q i).IsRationalPolytope) :
    ∃ K : ℕ,
      ∃ Qs : Fin K → Set (Fin (n + p) → ℝ),
        (∀ j : Fin K, (Qs j).IsRationalPolytope) ∧
          ((⋃ i : Fin k, Q i) ∩ firstBlockIntegerSet = ⋃ j : Fin K, Qs j) := by
  classical
  choose Kpiece Qpiece hQpiece hpiece using
    fun i : Fin k ↦ existsRationalPolytopeFirstBlockIntegerSlices (hQ i)
  let I := Σ i : Fin k, Fin (Kpiece i)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let Qs : Fin (Fintype.card I) → Set (Fin (n + p) → ℝ) :=
    fun j ↦ Qpiece (e.symm j).1 (e.symm j).2
  refine ⟨Fintype.card I, Qs, ?_, ?_⟩
  · intro j
    -- Each sigma-indexed piece comes from one rational-polytopal fiber of one original family
    -- member.
    exact hQpiece (e.symm j).1 (e.symm j).2
  · -- Reindex the per-piece slice covers by one sigma family.
    ext u
    constructor
    · intro hu
      rcases hu with ⟨huUnion, huInt⟩
      rcases Set.mem_iUnion.1 huUnion with ⟨i, hui⟩
      have huSlice : u ∈ Q i ∩ firstBlockIntegerSet := ⟨hui, huInt⟩
      have huPiece : u ∈ ⋃ j : Fin (Kpiece i), Qpiece i j := by
        rwa [hpiece i] at huSlice
      rcases Set.mem_iUnion.1 huPiece with ⟨j, huj⟩
      refine Set.mem_iUnion.2 ⟨e ⟨i, j⟩, ?_⟩
      let ij : I := e.symm (e ⟨i, j⟩)
      change u ∈ Qpiece ij.1 ij.2
      have hprop :
          (u ∈ Qpiece ij.1 ij.2) = (u ∈ Qpiece i j) := by
        dsimp [ij]
        simpa using congrArg (fun a : I ↦ u ∈ Qpiece a.1 a.2) (e.left_inv ⟨i, j⟩)
      exact Eq.mpr hprop huj
    · intro hu
      rcases Set.mem_iUnion.1 hu with ⟨j, huj⟩
      let ij : I := e.symm j
      have huSlice : u ∈ Q ij.1 ∩ firstBlockIntegerSet := by
        have huPiece : u ∈ ⋃ l : Fin (Kpiece ij.1), Qpiece ij.1 l := by
          exact Set.mem_iUnion.2 ⟨ij.2, by simpa [Qs, ij] using huj⟩
        rwa [← hpiece ij.1] at huPiece
      exact ⟨Set.mem_iUnion.2 ⟨ij.1, huSlice.1⟩, huSlice.2⟩

/-- Helper for Theorem 4.47: the auxiliary integer-variable matrix adds `±Id` rows for the first
flattened block and has zero ambient contribution on the original inequalities. -/
private def flatMixedIntegerWitnessIntMatrix
    {n m : ℕ} :
    Matrix (Fin (m + (n + n))) (Fin n) ℚ :=
  fun i ↦
    Fin.addCases
      (fun _ _ ↦ 0)
      (Fin.addCases
        (fun i' j ↦ if j = i' then 1 else 0)
        (fun i' j ↦ if j = i' then -1 else 0))
      i

/-- Helper for Theorem 4.47: the auxiliary real-variable matrix keeps the original flattened
polyhedron rows and adds `∓Id` rows on the first `n` real coordinates. -/
private def flatMixedIntegerWitnessRealMatrix
    {n p m : ℕ}
    (A : Matrix (Fin m) (Fin (n + p)) ℚ) :
    Matrix (Fin (m + (n + n))) (Fin (n + p)) ℚ :=
  fun i ↦
    Fin.addCases
      A
      (Fin.addCases
        (fun i' ↦ Fin.append (fun j ↦ if j = i' then -1 else 0) (fun _ ↦ 0))
        (fun i' ↦ Fin.append (fun j ↦ if j = i' then 1 else 0) (fun _ ↦ 0)))
      i

/-- Helper for Theorem 4.47: the lifted witness system reuses the original right-hand side and
uses zero on the equality rows. -/
private def flatMixedIntegerWitnessRhs
    {n m : ℕ}
    (b : Fin m → ℚ) :
    Fin (m + (n + n)) → ℚ :=
  Fin.addCases b (Fin.addCases (fun _ ↦ 0) (fun _ ↦ 0))

/-- Helper for Theorem 4.47: the first equality-row block of the integer witness matrix picks out
the chosen integer coordinate. -/
private lemma flatMixedIntegerWitnessIntFirstRow
    {n m : ℕ}
    (z : Fin n → ℤ)
    (i : Fin n) :
    (((flatMixedIntegerWitnessIntMatrix).map (Rat.castHom ℝ)) *ᵥ
        fun j ↦ (z j : ℝ)) (Fin.natAdd m (Fin.castAdd n i)) =
      (z i : ℝ) := by
  classical
  -- Evaluate the `+Id` row by isolating the unique nonzero coefficient at `i`.
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [flatMixedIntegerWitnessIntMatrix, Fin.addCases_right]
  · intro j _ hj
    simp [flatMixedIntegerWitnessIntMatrix, Fin.addCases_right, hj]
  · simp [flatMixedIntegerWitnessIntMatrix, Fin.addCases_right]

/-- Helper for Theorem 4.47: the second equality-row block of the integer witness matrix
contributes the negated chosen integer coordinate. -/
private lemma flatMixedIntegerWitnessIntSecondRow
    {n m : ℕ}
    (z : Fin n → ℤ)
    (i : Fin n) :
    (((flatMixedIntegerWitnessIntMatrix).map (Rat.castHom ℝ)) *ᵥ
        fun j ↦ (z j : ℝ)) (Fin.natAdd m (Fin.natAdd n i)) =
      -(z i : ℝ) := by
  classical
  -- Evaluate the `-Id` row by isolating the same coordinate with coefficient `-1`.
  have hcoeff :
      ∀ j : Fin n,
        (((flatMixedIntegerWitnessIntMatrix).map (Rat.castHom ℝ))
            (Fin.natAdd m (Fin.natAdd n i)) j) =
          if j = i then (-1 : ℝ) else 0 := by
    intro j
    have hnat : i.addNat n = Fin.natAdd n i := by
      apply Fin.ext
      simpa [Nat.add_comm] using rfl
    simp [flatMixedIntegerWitnessIntMatrix]
    rw [hnat, Fin.addCases_right]
    by_cases h : j = i <;> simp [h]
  rw [Matrix.mulVec, dotProduct]
  simp_rw [hcoeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- Helper for Theorem 4.47: the first equality-row block of the real witness matrix records the
negated first-block coordinate of the ambient point. -/
private lemma flatMixedIntegerWitnessRealFirstRow
    {n p m : ℕ}
    (A : Matrix (Fin m) (Fin (n + p)) ℚ)
    (u : Fin (n + p) → ℝ)
    (i : Fin n) :
    (((flatMixedIntegerWitnessRealMatrix A).map (Rat.castHom ℝ)) *ᵥ
        u) (Fin.natAdd m (Fin.castAdd n i)) =
      -u (Fin.castAdd p i) := by
  classical
  -- Split the flattened coordinates into the first `n` block and the trailing `p` block.
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Finset.sum_eq_single i]
  · simp [flatMixedIntegerWitnessRealMatrix, Fin.addCases_right]
  · intro j _ hj
    simp [flatMixedIntegerWitnessRealMatrix, Fin.addCases_right, hj]
  · simp [flatMixedIntegerWitnessRealMatrix, Fin.addCases_right]

/-- Helper for Theorem 4.47: the second equality-row block of the real witness matrix records the
first-block coordinate of the ambient point. -/
private lemma flatMixedIntegerWitnessRealSecondRow
    {n p m : ℕ}
    (A : Matrix (Fin m) (Fin (n + p)) ℚ)
    (u : Fin (n + p) → ℝ)
    (i : Fin n) :
    (((flatMixedIntegerWitnessRealMatrix A).map (Rat.castHom ℝ)) *ᵥ
        u) (Fin.natAdd m (Fin.natAdd n i)) =
      u (Fin.castAdd p i) := by
  classical
  -- The second equality block extracts the same coordinate with coefficient `+1`.
  have hcoeffLeft :
      ∀ j : Fin n,
        (((flatMixedIntegerWitnessRealMatrix A).map (Rat.castHom ℝ))
            (Fin.natAdd m (Fin.natAdd n i)) (Fin.castAdd p j)) =
          if j = i then (1 : ℝ) else 0 := by
    intro j
    have hnat : i.addNat n = Fin.natAdd n i := by
      apply Fin.ext
      simpa [Nat.add_comm] using rfl
    simp [flatMixedIntegerWitnessRealMatrix]
    rw [hnat, Fin.addCases_right]
    by_cases h : j = i <;> simp [h]
  have hcoeffRight :
      ∀ j : Fin p,
        (((flatMixedIntegerWitnessRealMatrix A).map (Rat.castHom ℝ))
            (Fin.natAdd m (Fin.natAdd n i)) (Fin.natAdd n j)) =
          0 := by
    intro j
    have hnat : i.addNat n = Fin.natAdd n i := by
      apply Fin.ext
      simpa [Nat.add_comm] using rfl
    simp [flatMixedIntegerWitnessRealMatrix]
    rw [hnat, Fin.addCases_right]
    simp
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  simp_rw [hcoeffLeft, hcoeffRight]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- Helper for Theorem 4.47: the second equality-row block of the lifted right-hand side is
zero. -/
private lemma flatMixedIntegerWitnessRhsSecondRow
    {n m : ℕ}
    (b : Fin m → ℚ)
    (i : Fin n) :
    (↑(flatMixedIntegerWitnessRhs b (Fin.natAdd m (Fin.natAdd n i))) : ℝ) = 0 := by
  have hnat : i.addNat n = Fin.natAdd n i := by
    apply Fin.ext
    simpa [Nat.add_comm] using rfl
  simp [flatMixedIntegerWitnessRhs]
  rw [hnat, Fin.addCases_right]

/-- Helper for Theorem 4.47: membership in the lifted witness polyhedron is exactly ambient
flattened feasibility together with the equalities tying the integer variables to the first block.
-/
private lemma memFlatMixedIntegerWitnessPolyhedron_iff
    {n p m : ℕ}
    {A : Matrix (Fin m) (Fin (n + p)) ℚ}
    {b : Fin m → ℚ}
    {z : Fin n → ℤ}
    {u : Fin (n + p) → ℝ} :
    ((fun i ↦ (z i : ℝ)), u) ∈
        rational_mixed_polyhedron
          (flatMixedIntegerWitnessIntMatrix)
          (flatMixedIntegerWitnessRealMatrix A)
          (flatMixedIntegerWitnessRhs b) ↔
      u ∈ polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) ∧
        (fun i : Fin n ↦ u (Fin.castAdd p i)) = fun i ↦ (z i : ℝ) := by
  rw [mem_rational_mixed_polyhedron_iff, mem_polyhedron_le_set_iff]
  constructor
  · intro h
    constructor
    · -- The leading `m` rows are exactly the original ambient inequalities.
      intro i
      have hi := h (Fin.castAdd (n + n) i)
      simpa [flatMixedIntegerWitnessIntMatrix, flatMixedIntegerWitnessRealMatrix,
        flatMixedIntegerWitnessRhs, Matrix.mulVec, dotProduct, Fin.sum_univ_add] using hi
    · -- The two `±Id` row blocks force equality between `z` and the first `n` coordinates.
      funext i
      apply le_antisymm
      · have hi := h (Fin.natAdd m (Fin.natAdd n i))
        have hIntRow := flatMixedIntegerWitnessIntSecondRow (m := m) z i
        have hRealRow := flatMixedIntegerWitnessRealSecondRow (m := m) A u i
        rw [Pi.add_apply, hIntRow, hRealRow] at hi
        have hRhs :
            (fun j ↦ (flatMixedIntegerWitnessRhs b j : ℝ))
                (Fin.natAdd m (Fin.natAdd n i)) = 0 := by
          simpa using flatMixedIntegerWitnessRhsSecondRow (n := n) b i
        rw [hRhs] at hi
        have hi' : -(z i : ℝ) + u (Fin.castAdd p i) ≤ 0 := by
          exact hi
        -- The `u_i - z_i ≤ 0` inequality gives `u_i ≤ z_i`.
        have hi'' : u (Fin.castAdd p i) ≤ (z i : ℝ) := by
          linarith
        exact hi''
      · have hi := h (Fin.natAdd m (Fin.castAdd n i))
        have hIntRow := flatMixedIntegerWitnessIntFirstRow (m := m) z i
        have hRealRow := flatMixedIntegerWitnessRealFirstRow (m := m) A u i
        rw [Pi.add_apply, hIntRow, hRealRow] at hi
        have hi' : (z i : ℝ) + -u (Fin.castAdd p i) ≤ 0 := by
          simpa [flatMixedIntegerWitnessRhs] using hi
        -- The `z_i - u_i ≤ 0` inequality gives `z_i ≤ u_i`.
        have hi'' : (z i : ℝ) ≤ u (Fin.castAdd p i) := by
          linarith
        exact hi''
  · rintro ⟨hu, huz⟩
    intro i
    -- Split the witness rows into the ambient block and the two equality blocks.
    refine Fin.addCases ?_ ?_ i
    · intro j
      have hj := hu j
      simpa [flatMixedIntegerWitnessIntMatrix, flatMixedIntegerWitnessRealMatrix,
        flatMixedIntegerWitnessRhs, Matrix.mulVec, dotProduct, Fin.sum_univ_add] using hj
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j'
        have hj' : u (Fin.castAdd p j') = (z j' : ℝ) := congrFun huz j'
        have hIntRow := flatMixedIntegerWitnessIntFirstRow (m := m) z j'
        have hRealRow := flatMixedIntegerWitnessRealFirstRow (m := m) A u j'
        have hrow : (z j' : ℝ) + -u (Fin.castAdd p j') ≤ 0 := by
          simpa [hj']
        -- Repackage the coordinate equality as the corresponding equality-row inequality.
        rw [Pi.add_apply, hIntRow, hRealRow]
        simpa [flatMixedIntegerWitnessRhs] using hrow
      · intro j'
        have hj' : u (Fin.castAdd p j') = (z j' : ℝ) := congrFun huz j'
        have hIntRow := flatMixedIntegerWitnessIntSecondRow (m := m) z j'
        have hRealRow := flatMixedIntegerWitnessRealSecondRow (m := m) A u j'
        have hrow : -(z j' : ℝ) + u (Fin.castAdd p j') ≤ 0 := by
          simpa [hj']
        -- Repackage the same coordinate equality for the second equality-row block.
        rw [Pi.add_apply, hIntRow, hRealRow]
        have hRhs :
            (fun j ↦ (flatMixedIntegerWitnessRhs b j : ℝ))
                (Fin.natAdd m (Fin.natAdd n j')) = 0 := by
          simpa using flatMixedIntegerWitnessRhsSecondRow (n := n) b j'
        rw [hRhs]
        exact hrow

/-- Helper for Theorem 4.47: the flattened mixed-integer set is the `x`-projection of the explicit
normalized witness polyhedron built from the flattened ambient matrix presentation. -/
private lemma exists_explicitFlatMixedIntegerProjectionWitness
    {n p : ℕ}
    (P : Set (MixedRealPoint n p))
    (hP : is_rational_mixed_polyhedron P) :
    ∃ W : Set (MixedRealPoint n (n + p)),
      is_rational_mixed_polyhedron W ∧
        Fin.appendEquiv n p '' mixed_integer_points P =
          mixed_integer_x_projection (n := n + p) (p := 0) (q := n) W := by
  rcases (show is_rational_polyhedron ((Fin.appendEquiv n p) '' P) from hP) with
    ⟨m, A, b, hPflat_eq⟩
  let W : Set (MixedRealPoint n (n + p)) :=
    rational_mixed_polyhedron
      (flatMixedIntegerWitnessIntMatrix)
      (flatMixedIntegerWitnessRealMatrix A)
      (flatMixedIntegerWitnessRhs b)
  refine ⟨W, ?_, ?_⟩
  · -- The witness polyhedron is rational by construction.
    refine (is_rational_mixed_polyhedron_iff).2 ?_
    refine ⟨m + (n + n), flatMixedIntegerWitnessIntMatrix,
      flatMixedIntegerWitnessRealMatrix A,
      flatMixedIntegerWitnessRhs b, rfl⟩
  · -- Identify the flattened mixed-integer set with the witness `x`-projection.
    ext u
    rw [mem_mixed_integer_x_projection_iff]
    constructor
    · intro hu
      rcases (memFlatMixedIntegerPoints_iff).1 hu with ⟨huP, huZ⟩
      rw [hPflat_eq] at huP
      rcases (mem_integerVectors_iff).1 huZ
        with ⟨z, hz⟩
      refine ⟨(fun j : Fin 0 ↦ Fin.elim0 j), z, ?_⟩
      have hwitness : ((fun j ↦ (z j : ℝ)), u) ∈ W := by
        rw [memFlatMixedIntegerWitnessPolyhedron_iff]
        exact ⟨huP, hz⟩
      simpa [W] using hwitness
    · rintro ⟨y, z, hzW⟩
      have hyappend : Fin.append u y = u := by
        funext i
        simpa using Fin.append_left u y i
      have hzWitness :
          ((fun j ↦ (z j : ℝ)), u) ∈
            rational_mixed_polyhedron
              (flatMixedIntegerWitnessIntMatrix)
              (flatMixedIntegerWitnessRealMatrix A)
              (flatMixedIntegerWitnessRhs b) := by
        simpa [W, hyappend] using hzW
      have hzW' :=
        (memFlatMixedIntegerWitnessPolyhedron_iff).1 hzWitness
      have huP : u ∈ Fin.appendEquiv n p '' P := by
        rw [hPflat_eq]
        simpa using hzW'.1
      have huZ : (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
        refine (mem_integerVectors_iff).2 ?_
        refine ⟨z, ?_⟩
        funext i
        have hi := congrFun hzW'.2 i
        simpa using hi
      exact (memFlatMixedIntegerPoints_iff).2 ⟨huP, huZ⟩

/-- Helper for Theorem 4.47: the empty set is mixed integer linear representable. -/
lemma empty_is_mixed_integer_linear_representable
    {n : ℕ} :
    is_mixed_integer_linear_representable (∅ : Set (Fin n → ℝ)) := by
  -- Use one impossible inequality `0 ≤ -1` so the projection has no feasible lifted witness.
  rw [is_mixed_integer_linear_representable_iff]
  let P : Set (MixedRealPoint 0 (n + 0)) :=
    rational_mixed_polyhedron
      (fun _ _ ↦ (0 : ℚ))
      (fun _ _ ↦ (0 : ℚ))
      (fun _ : Fin 1 ↦ (-1 : ℚ))
  refine ⟨0, 0, P, ?_, ?_⟩
  · -- The witness set is rational because it is already given by a rational mixed system.
    exact (is_rational_mixed_polyhedron_iff).2
      ⟨1,
        (fun _ _ ↦ (0 : ℚ)),
        (fun _ _ ↦ (0 : ℚ)),
        (fun _ : Fin 1 ↦ (-1 : ℚ)),
        rfl⟩
  · -- The unique inequality row reduces every would-be witness to the contradiction `0 ≤ -1`.
    ext x
    rw [mem_mixed_integer_x_projection_iff]
    constructor
    · intro hx
      exact False.elim hx
    · rintro ⟨y, z, hzP⟩
      have hzero_le :
          (0 : ℝ) ≤ -1 := by
        have hrow := ((mem_rational_mixed_polyhedron_iff).1 hzP) 0
        simpa [P, Matrix.mulVec, dotProduct] using hrow
      have : False := by
        linarith
      exact this.elim

/-- Helper for Theorem 4.47: a finite union of rational polytope pieces translated by one
finitely generated integral cone is mixed integer linear representable. -/
private lemma mixedIntegerLinearRepresentable_of_unionRationalPolytopesAddIntegralIntcone
    {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS :
      ∃ k t : ℕ,
        ∃ P : Fin k → Set (Fin n → ℝ),
          ∃ r : Fin t → Fin n → ℤ,
            (∀ i : Fin k, (P i).IsRationalPolytope) ∧
              S = (⋃ i : Fin k, P i) + integral_intcone r) :
    is_mixed_integer_linear_representable S := by
  rcases hS with ⟨k, t, P, r, hP, hrepr⟩
  rcases exists_reindexedNonemptyRationalPolytopeFamily P hP with
    ⟨k', P', hP', hP'_nonempty, hUnion⟩
  rcases exists_rationalMatrixPolyhedronDescriptions hP' with
    ⟨m, A, b, hAb⟩
  have hPoly :
      ∀ i : Fin k', (rational_matrix_polyhedron (A i) (b i)).IsRationalPolytope := by
    intro i
    rw [← hAb i]
    exact hP' i
  have hNonempty :
      ∀ i : Fin k', (rational_matrix_polyhedron (A i) (b i)).Nonempty := by
    intro i
    rw [← hAb i]
    exact hP'_nonempty i
  have hUnionMatrix :
      (⋃ i : Fin k', P' i) = ⋃ i : Fin k', rational_matrix_polyhedron (A i) (b i) := by
    -- Rewrite each reindexed rational polytope piece by its chosen rational matrix description.
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      rw [hAb i] at hxi
      exact hxi
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      rw [hAb i]
      exact hxi
  have hProj :
      mixed_integer_x_projection (selectorConeWitnessPolyhedron m A b r) =
        (⋃ i : Fin k', rational_matrix_polyhedron (A i) (b i)) + integral_intcone r := by
    -- The direct selector/cone witness projects exactly to the matrix-described union-plus-cone
    -- surface.
    ext x
    exact mem_selectorConeWitnessProjection_iff m A b r hPoly hNonempty
  rw [is_mixed_integer_linear_representable_iff]
  refine ⟨selectorConeRealAuxDim k' n, k' + t, selectorConeWitnessPolyhedron m A b r, ?_, ?_⟩
  · -- The selector/cone witness is rational mixed polyhedral by construction.
    exact selectorConeWitnessPolyhedron_isRationalMixedPolyhedron m A b r
  · -- Compare the source union-plus-cone description to the selector-lift projection.
    calc
      S = (⋃ i : Fin k, P i) + integral_intcone r := hrepr
      _ = (⋃ i : Fin k', P' i) + integral_intcone r := by
        rw [hUnion]
      _ = (⋃ i : Fin k', rational_matrix_polyhedron (A i) (b i)) + integral_intcone r := by
        rw [hUnionMatrix]
      _ = mixed_integer_x_projection (selectorConeWitnessPolyhedron m A b r) := hProj.symm

/-- Helper for Theorem 4.47: once the flattened mixed-integer witness is decomposed on the
ambient space, the visible `x`-projection has the required union-of-rational-polytopes-plus-cone
form. -/
private lemma unionRationalPolytopesAddIntegralIntcone_ofRepresentableWitness
    {n p q : ℕ}
    {P : Set (MixedRealPoint q (n + p))}
    {S : Set (Fin n → ℝ)}
    (hSP : S = mixed_integer_x_projection P)
    (hflat :
      ∃ k t : ℕ,
        ∃ Q : Fin k → Set (Fin (q + (n + p)) → ℝ),
          ∃ r : Fin t → Fin (q + (n + p)) → ℤ,
            (∀ i : Fin k, (Q i).IsRationalPolytope) ∧
              Fin.appendEquiv q (n + p) '' mixed_integer_points P =
                (⋃ i : Fin k, Q i) + integral_intcone r) :
    ∃ k t : ℕ,
      ∃ P' : Fin k → Set (Fin n → ℝ),
        ∃ r' : Fin t → Fin n → ℤ,
          (∀ i : Fin k, (P' i).IsRationalPolytope) ∧
            S = (⋃ i : Fin k, P' i) + integral_intcone r' := by
  rcases exists_unionRationalPolytopesAddIntegralIntcone_ofMixedIntegerWitness hflat with
    ⟨k, t, P', r', hP', hrepr⟩
  -- Rewrite the transported `x`-projection decomposition back to the user-facing set `S`.
  exact ⟨k, t, P', r', hP', by simpa [hSP] using hrepr⟩

/-- Helper for Theorem 4.47: the flattened mixed-integer witness should admit the finite
union-plus-integral-cone decomposition used in the forward direction. -/
private lemma existsFlatMixedIntegerWitnessDecomposition_of_empty
    {n p q : ℕ}
    {P : Set (MixedRealPoint q (n + p))}
    (hPempty : mixed_integer_points P = ∅) :
    ∃ k t : ℕ,
      ∃ Q : Fin k → Set (Fin (q + (n + p)) → ℝ),
        ∃ r : Fin t → Fin (q + (n + p)) → ℤ,
          (∀ i : Fin k, (Q i).IsRationalPolytope) ∧
            Fin.appendEquiv q (n + p) '' mixed_integer_points P =
              (⋃ i : Fin k, Q i) + integral_intcone r := by
  refine ⟨0, 0, Fin.elim0, Fin.elim0, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · -- If there are no mixed-integer points, the flattened witness is the empty union.
    ext u
    simp [hPempty, integral_intcone]

/-- Helper for Theorem 4.47: every rational vector has a positive common denominator. -/
private lemma rationalVectorCommonDenominator_ne_zero
    {n : ℕ}
    (v : Fin n → ℚ) :
    rational_vector_common_denominator v ≠ 0 := by
  have hden :
      ∀ i ∈ (Finset.univ : Finset (Fin n)), (v i).den ≠ 0 := by
    intro i hi
    exact Nat.ne_of_gt (Rat.den_pos (v i))
  simpa [rational_vector_common_denominator] using
    (Finset.lcm_ne_zero_iff.2 hden)

/-- Helper for Theorem 4.47: clearing denominators rescales a rational vector by its common
denominator. -/
private lemma commonDenominatorScaledVector_eq_smulReal
    {n : ℕ}
    (v : Fin n → ℚ) :
    (fun i ↦ ((common_denominator_scaled_vector v) i : ℝ)) =
      (rational_vector_common_denominator v : ℝ) • (fun i ↦ (v i : ℝ)) := by
  ext i
  change ((common_denominator_scaled_vector v i : ℤ) : ℝ) =
      (rational_vector_common_denominator v : ℝ) * (v i : ℝ)
  have hi :
      ((common_denominator_scaled_vector v i : ℤ) : ℚ) =
        (rational_vector_common_denominator v : ℚ) * v i := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      congrFun (common_denominator_scaled_vector_eq_smul v) i
  exact_mod_cast hi

/-- Helper for Theorem 4.47: clearing denominators on every rational ray does not change the
generated cone. -/
private lemma commonDenominatorScaledRays_eq_finitelyGeneratedCone
    {k q : ℕ}
    (r : Fin q → Fin k → ℚ) :
    finitely_generated_cone
        (fun j : Fin q ↦ fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) =
      finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, hrepr⟩
    have hD_nonneg :
        ∀ j : Fin q, 0 ≤ (rational_vector_common_denominator (r j) : ℝ) := by
      intro j
      exact_mod_cast Nat.zero_le (rational_vector_common_denominator (r j))
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j * (rational_vector_common_denominator (r j) : ℝ), ?_, ?_⟩
    · intro j
      exact mul_nonneg (hμ_nonneg j) (hD_nonneg j)
    · calc
        x = ∑ j : Fin q, μ j • (fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) :=
              hrepr
        _ = ∑ j : Fin q,
              (μ j * (rational_vector_common_denominator (r j) : ℝ)) •
                (fun i : Fin k ↦ (r j i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [commonDenominatorScaledVector_eq_smulReal (v := r j), smul_smul]
  · intro x hx
    rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, hrepr⟩
    have hD_nonneg :
        ∀ j : Fin q, 0 ≤ (rational_vector_common_denominator (r j) : ℝ) := by
      intro j
      exact_mod_cast Nat.zero_le (rational_vector_common_denominator (r j))
    have hD_ne_zero :
        ∀ j : Fin q, (rational_vector_common_denominator (r j) : ℝ) ≠ 0 := by
      intro j
      exact_mod_cast rationalVectorCommonDenominator_ne_zero (r j)
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j / (rational_vector_common_denominator (r j) : ℝ), ?_, ?_⟩
    · intro j
      exact div_nonneg (hμ_nonneg j) (hD_nonneg j)
    · calc
        x = ∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ)) := hrepr
        _ = ∑ j : Fin q,
              (μ j / (rational_vector_common_denominator (r j) : ℝ)) •
                (fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [commonDenominatorScaledVector_eq_smulReal (v := r j), smul_smul,
                div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (hD_ne_zero j), mul_one]

/-- Helper for Theorem 4.47: a nonempty flattened rational mixed polyhedron admits finitely many
integral generators for its recession cone without importing the cyclic Section 4.8 owner. -/
private lemma existsFlattenedIntegralRecessionGenerators
    {n p : ℕ}
    {P : Set (MixedRealPoint n p)}
    (hP : is_rational_mixed_polyhedron P)
    (hP_nonempty : Set.Nonempty P) :
    ∃ q : ℕ,
      ∃ rays : Fin q → Fin (n + p) → ℤ,
        recessionCone ((Fin.appendEquiv n p) '' P) =
          finitely_generated_cone (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (rays j i : ℝ)) := by
  rcases (show is_rational_polyhedron ((Fin.appendEquiv n p) '' P) from hP) with
    ⟨m, A, b, hPflat_eq⟩
  have hPflat_nonempty :
      Set.Nonempty (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) := by
    rcases hP_nonempty with ⟨w, hw⟩
    have hwImage : Fin.appendEquiv n p w ∈ Fin.appendEquiv n p '' P := ⟨w, hw, rfl⟩
    rw [hPflat_eq] at hwImage
    exact ⟨Fin.appendEquiv n p w, hwImage⟩
  rcases exists_rational_matrix_cone_of_rational_matrix_polyhedral_cone A with ⟨q, R, hR⟩
  let raysQ : Fin q → Fin (n + p) → ℚ := fun j i ↦ R i j
  let raysInt : Fin q → Fin (n + p) → ℤ := fun j ↦ common_denominator_scaled_vector (raysQ j)
  refine ⟨q, raysInt, ?_⟩
  -- Normalize the homogeneous recession system to a rational matrix cone, then clear
  -- denominators on each rational generator once.
  calc
    recessionCone ((Fin.appendEquiv n p) '' P)
        = recessionCone (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) := by
            rw [hPflat_eq]
    _ = matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) := by
          simpa [matrix_polyhedral_cone] using
            polyhedron_recessionCone_eq_homogeneous_solution_set
              (A.map (Rat.castHom ℝ))
              (fun i ↦ (b i : ℝ))
              hPflat_nonempty
    _ = (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin (n + p) → ℝ)) := hR
    _ = finitely_generated_cone (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (raysQ j i : ℝ)) := by
          simpa [raysQ] using
            (finitely_generated_cone_eq_matrix_cone
              (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (raysQ j i : ℝ))).symm
    _ = finitely_generated_cone (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (raysInt j i : ℝ)) := by
          simpa [raysInt, raysQ] using
            (commonDenominatorScaledRays_eq_finitelyGeneratedCone (r := raysQ)).symm

/-- Helper for Theorem 4.47: the coefficient unit box is a rational polytope. -/
private lemma coefficientUnitBox_isRationalPolytope
    (q : ℕ) :
    (Set.univ.pi (fun _ : Fin q ↦ Set.Icc (0 : ℝ) 1)).IsRationalPolytope :=
  unitBox_isRationalPolytope q

/-- Helper for Theorem 4.47: the fractional coefficient box for an integral ray family is the
image of the unit box under the corresponding rational linear map. -/
private def fractionalRayBox
    {k q : ℕ}
    (rays : Fin q → Fin k → ℤ) :
    Set (Fin k → ℝ) :=
  (fun μ : Fin q → ℝ ↦ ∑ j : Fin q, μ j • (fun i : Fin k ↦ (rays j i : ℝ))) ''
    Set.univ.pi (fun _ : Fin q ↦ Set.Icc (0 : ℝ) 1)

/-- Helper for Theorem 4.47: the fractional coefficient box of an integral ray family is a
rational polytope. -/
private lemma fractionalRayBox_isRationalPolytope
    {k q : ℕ}
    (rays : Fin q → Fin k → ℤ) :
    (fractionalRayBox rays).IsRationalPolytope := by
  let A : Matrix (Fin k) (Fin q) ℚ := fun i j ↦ (rays j i : ℚ)
  have himage :
      fractionalRayBox rays =
        (fun μ : Fin q → ℝ ↦ (A.map (Rat.castHom ℝ)) *ᵥ μ) ''
          Set.univ.pi (fun _ : Fin q ↦ Set.Icc (0 : ℝ) 1) := by
    ext x
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      refine ⟨μ, hμ, ?_⟩
      ext i
      simp [A, Matrix.mulVec, dotProduct, mul_comm]
    · rintro ⟨μ, hμ, rfl⟩
      refine ⟨μ, hμ, ?_⟩
      ext i
      simp [A, Matrix.mulVec, dotProduct, mul_comm]
  rw [himage]
  exact isRationalPolytope_image_rationalMatrixMulVec
    (coefficientUnitBox_isRationalPolytope q) A

/-- Helper for Theorem 4.47: the real cone generated by integral rays splits into a bounded
fractional part plus the integral cone. -/
private lemma finitelyGeneratedCone_eq_fractionalRayBox_add_integralIntcone
    {k q : ℕ}
    (rays : Fin q → Fin k → ℤ) :
    finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (rays j i : ℝ)) =
      fractionalRayBox rays + integral_intcone rays := by
  ext x
  constructor
  · intro hx
    rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, hrepr⟩
    let a : Fin q → ℕ := fun j ↦ Int.toNat (Int.floor (μ j))
    let frac : Fin q → ℝ := fun j ↦ μ j - a j
    have ha_nonneg_int : ∀ j : Fin q, 0 ≤ Int.floor (μ j) := by
      intro j
      exact Int.floor_nonneg.mpr (hμ_nonneg j)
    have ha_cast : ∀ j : Fin q, ((a j : ℕ) : ℝ) = Int.floor (μ j) := by
      intro j
      have hcastInt : (((a j : ℕ) : ℤ)) = Int.floor (μ j) := by
        simp [a, Int.toNat_of_nonneg (ha_nonneg_int j)]
      exact_mod_cast hcastInt
    have hfrac_mem :
        frac ∈ Set.univ.pi (fun _ : Fin q ↦ Set.Icc (0 : ℝ) 1) := by
      rw [Set.mem_univ_pi]
      intro j
      constructor
      · have hfloor_le : (Int.floor (μ j) : ℝ) ≤ μ j := by
          exact_mod_cast Int.floor_le (μ j)
        have hcast := ha_cast j
        dsimp [frac]
        linarith
      · have hlt : μ j < Int.floor (μ j) + 1 := by
          exact Int.lt_floor_add_one (μ j)
        have hcast := ha_cast j
        dsimp [frac]
        linarith
    refine Set.mem_add.2 ?_
    refine ⟨∑ j : Fin q, frac j • (fun i : Fin k ↦ (rays j i : ℝ)), ?_,
      ∑ j : Fin q, (a j : ℝ) • (fun i : Fin k ↦ (rays j i : ℝ)), ?_, ?_⟩
    · -- The fractional coefficients stay in the bounded unit box.
      exact ⟨frac, hfrac_mem, rfl⟩
    · -- The floored coefficients give the integral cone contribution.
      exact (mem_integral_intcone_iff).2 ⟨a, rfl⟩
    · -- Split each nonnegative coefficient into its floor and fractional part.
      have hsplit : ∀ j : Fin q, μ j = frac j + (a j : ℝ) := by
        intro j
        dsimp [frac]
        linarith [ha_cast j]
      ext i
      rw [hrepr]
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
      calc
        ∑ c : Fin q, frac c * (rays c i : ℝ) + ∑ c : Fin q, (a c : ℝ) * (rays c i : ℝ)
            = ∑ c : Fin q, (frac c + (a c : ℝ)) * (rays c i : ℝ) := by
                simp [add_mul, Finset.sum_add_distrib]
        _ = ∑ c : Fin q, μ c * (rays c i : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [← hsplit j]
  · rintro ⟨u, hu, c, hc, rfl⟩
    rcases hu with ⟨μ, hμ, rfl⟩
    rcases (mem_integral_intcone_iff).1 hc with ⟨a, rfl⟩
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j + a j, ?_, ?_⟩
    · intro j
      have hμj : μ j ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.mem_univ_pi] using hμ j
      exact add_nonneg hμj.1 (by exact_mod_cast Nat.zero_le (a j))
    · ext i
      simp [Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib]

/-- Helper for Theorem 4.47: once the recession rays are integral, the ambient flattened witness
can be normalized to one rational polytope plus one integral cone. -/
private lemma flatAmbient_eq_rationalPolytope_add_integralIntcone_of_nonempty
    {n p : ℕ}
    {W : Set (MixedRealPoint n p)}
    (hW : is_rational_mixed_polyhedron W)
    (hW_nonempty : Set.Nonempty W) :
    ∃ t : ℕ,
      ∃ Q0 : Set (Fin (n + p) → ℝ),
        ∃ r : Fin t → Fin (n + p) → ℤ,
          Q0.IsRationalPolytope ∧
            Fin.appendEquiv n p '' W = Q0 + integral_intcone r := by
  let Pflat : Set (Fin (n + p) → ℝ) := Fin.appendEquiv n p '' W
  have hPflat_rational : is_rational_polyhedron Pflat := by
    simpa [Pflat] using (show is_rational_polyhedron (Fin.appendEquiv n p '' W) from hW)
  have hPflat_nonempty : Set.Nonempty Pflat := by
    rcases hW_nonempty with ⟨w, hw⟩
    exact ⟨Fin.appendEquiv n p w, ⟨w, hw, rfl⟩⟩
  rcases existsFlattenedIntegralRecessionGenerators hW hW_nonempty with ⟨t, r, hrec⟩
  rcases existsFlattenedRationalVertexPresentationCompatibleWithIntegralRays
      hPflat_rational hPflat_nonempty r hrec with
    ⟨s, vQ, hQbase_repr⟩
  let Qbase : Set (Fin (n + p) → ℝ) :=
    convexHull ℝ (Set.range (fun i : Fin s ↦ fun u : Fin (n + p) ↦ (vQ i u : ℝ)))
  have hQbase : Qbase.IsRationalPolytope := by
    exact ⟨s, vQ, rfl⟩
  refine ⟨t, Qbase + fractionalRayBox r, r, isRationalPolytope_add hQbase
    (fractionalRayBox_isRationalPolytope r), ?_⟩
  -- Route correction: absorb the bounded fractional coefficients into one extra rational
  -- polytope instead of importing the unavailable ambient owner.
  calc
    Fin.appendEquiv n p '' W
        = Qbase + finitely_generated_cone (fun j : Fin t ↦ fun i : Fin (n + p) ↦ (r j i : ℝ)) :=
          by simpa [Qbase] using hQbase_repr
    _ = Qbase + (fractionalRayBox r + integral_intcone r) := by
          rw [finitelyGeneratedCone_eq_fractionalRayBox_add_integralIntcone]
    _ = (Qbase + fractionalRayBox r) + integral_intcone r := by
          ext x
          constructor
          · rintro ⟨u, hu, v, hv, rfl⟩
            rcases hv with ⟨w, hw, c, hc, rfl⟩
            exact Set.mem_add.2 ⟨u + w, Set.mem_add.2 ⟨u, hu, w, hw, rfl⟩, c, hc, by
              ext i
              simp [add_assoc]⟩
          · rintro ⟨u, hu, c, hc, rfl⟩
            rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
            exact Set.mem_add.2 ⟨u₁, hu₁, u₂ + c, Set.mem_add.2 ⟨u₂, hu₂, c, hc, rfl⟩, by
              ext i
              simp [add_assoc]⟩

/-- Helper for Theorem 4.47: the Section 4.8 compatible-vertex theorem can be repackaged as a
single rational-polytope bounded piece together with the fixed integral recession rays. -/
private lemma existsRationalPolytopePieceCompatibleWithIntegralRays
    {k q : ℕ}
    {Pflat : Set (Fin k → ℝ)}
    (hPflat_rational : is_rational_polyhedron Pflat)
    (hPflat_nonempty : Set.Nonempty Pflat)
    (rays : Fin q → Fin k → ℤ)
    (hrec_integral :
      recessionCone Pflat =
        finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (rays j i : ℝ))) :
    ∃ Q : Set (Fin k → ℝ),
      Q.IsRationalPolytope ∧
        Pflat = Q +
          finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (rays j i : ℝ)) := by
  -- Use the Section 4.8 owner theorem to keep the integral recession rays fixed while replacing
  -- the bounded part by a rational vertex presentation.
  rcases existsFlattenedRationalVertexPresentationCompatibleWithIntegralRays
      hPflat_rational hPflat_nonempty rays hrec_integral with
    ⟨t, vℚ, hrepr⟩
  refine ⟨convexHull ℝ (Set.range (fun i : Fin t ↦ fun u : Fin k ↦ (vℚ i u : ℝ))), ?_, hrepr⟩
  -- The bounded part is rational by construction from rational vertices.
  exact ⟨t, vℚ, rfl⟩

/-- Helper for Theorem 4.47: the flattened mixed-integer witness should admit the finite
union-plus-integral-cone decomposition used in the forward direction. -/
private lemma flatMixedIntegerPoints_eq_iUnion_rationalPolytopes_add_integralIntcone
    {n p : ℕ}
    {P : Set (MixedRealPoint n p)}
    (hP : is_rational_mixed_polyhedron P) :
    ∃ k t : ℕ,
      ∃ Q : Fin k → Set (Fin (n + p) → ℝ),
        ∃ r : Fin t → Fin (n + p) → ℤ,
          (∀ i : Fin k, (Q i).IsRationalPolytope) ∧
            Fin.appendEquiv n p '' mixed_integer_points P =
              (⋃ i : Fin k, Q i) + integral_intcone r := by
  by_cases hPempty : mixed_integer_points P = ∅
  · -- The empty flattened mixed-integer set is already handled by the explicit zero-family
    -- decomposition used in the forward implication.
    simpa [Nat.zero_add] using
      existsFlatMixedIntegerWitnessDecomposition_of_empty (n := p) (p := 0) (q := n)
        (P := P) hPempty
  · rcases exists_explicitFlatMixedIntegerProjectionWitness P hP with ⟨W, hW, hWproj⟩
    have hWflat :
        ∃ k t : ℕ,
          ∃ Q : Fin k → Set (Fin (n + (n + p)) → ℝ),
            ∃ r : Fin t → Fin (n + (n + p)) → ℤ,
              (∀ i : Fin k, (Q i).IsRationalPolytope) ∧
                Fin.appendEquiv n (n + p) '' mixed_integer_points W =
                  (⋃ i : Fin k, Q i) + integral_intcone r := by
      have hW_nonempty : Set.Nonempty W := by
        have hP_nonempty : Set.Nonempty (mixed_integer_points P) :=
          Set.nonempty_iff_ne_empty.mpr hPempty
        rcases hP_nonempty with ⟨w, hw⟩
        have hwproj :
            Fin.appendEquiv n p w ∈
              mixed_integer_x_projection (n := n + p) (p := 0) (q := n) W := by
          rw [← hWproj]
          exact ⟨w, hw, rfl⟩
        rcases (mem_mixed_integer_x_projection_iff).1 hwproj with ⟨y, z, hzW⟩
        have hy : Fin.append (Fin.appendEquiv n p w) y = Fin.appendEquiv n p w := by
          funext i
          simpa using Fin.append_left (Fin.appendEquiv n p w) y i
        refine ⟨((fun j ↦ (z j : ℝ)), Fin.appendEquiv n p w), ?_⟩
        simpa [hy] using hzW
      rcases flatAmbient_eq_rationalPolytope_add_integralIntcone_of_nonempty hW hW_nonempty with
        ⟨t, Qflat, r, hQflat, hWambient⟩
      have hWslice :
          Fin.appendEquiv n (n + p) '' mixed_integer_points W =
            (Qflat ∩ firstBlockIntegerSet) + integral_intcone r := by
        -- Rewrite the flattened mixed-integer set through the ambient decomposition before
        -- replacing the bounded integer slice by finitely many rational-polytopal fibers.
        simpa using
          flatMixedIntegerPoints_eq_baseSlice_add_integralIntcone
            hWambient
      rcases
        existsRationalPolytopeFirstBlockIntegerSlices hQflat with
        ⟨K, Qslice, hQslice, hslice⟩
      refine ⟨K, t, Qslice, r, hQslice, ?_⟩
      calc
        Fin.appendEquiv n (n + p) '' mixed_integer_points W
            = (Qflat ∩ firstBlockIntegerSet) + integral_intcone r := hWslice
        _ = (⋃ j : Fin K, Qslice j) + integral_intcone r := by
              rw [hslice]
    -- Once the witness `W` is decomposed in flattened coordinates, the existing projection
    -- transport package rewrites the witness decomposition back to the target set.
    exact
      unionRationalPolytopesAddIntegralIntcone_ofRepresentableWitness
        hWproj hWflat

/-- Helper for Theorem 4.47: the flattened mixed-integer witness should admit the finite
union-plus-integral-cone decomposition used in the forward direction. -/
private lemma existsFlatMixedIntegerWitnessDecomposition
    {n p q : ℕ}
    {P : Set (MixedRealPoint q (n + p))}
    (hP : is_rational_mixed_polyhedron P) :
    ∃ k t : ℕ,
      ∃ Q : Fin k → Set (Fin (q + (n + p)) → ℝ),
        ∃ r : Fin t → Fin (q + (n + p)) → ℤ,
          (∀ i : Fin k, (Q i).IsRationalPolytope) ∧
            Fin.appendEquiv q (n + p) '' mixed_integer_points P =
              (⋃ i : Fin k, Q i) + integral_intcone r := by
  -- The local forward direction is now reduced to the canonical flattened owner theorem.
  simpa using flatMixedIntegerPoints_eq_iUnion_rationalPolytopes_add_integralIntcone hP

/-- Theorem 4.47. A set `S ⊆ ℝ^n` is mixed integer linear representable if and only if it is a
finite union of rational polytopes translated by one finitely generated integer cone. -/
theorem mixed_integer_linear_representable_iff_union_rational_polytopes_add_integral_intcone
    {n : ℕ} (S : Set (Fin n → ℝ)) :
    is_mixed_integer_linear_representable S ↔
      ∃ k t : ℕ,
        ∃ P : Fin k → Set (Fin n → ℝ),
          ∃ r : Fin t → Fin n → ℤ,
            (∀ i : Fin k, (P i).IsRationalPolytope) ∧
              S = (⋃ i : Fin k, P i) + integral_intcone r := by
  constructor
  · intro hrepr
    by_cases hSempty : S = ∅
    · -- The empty set is the empty union translated by the trivial cone.
      refine ⟨0, 0, Fin.elim0, Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · ext x
        simp [hSempty, integral_intcone]
    · rcases (is_mixed_integer_linear_representable_iff).1 hrepr with
        ⟨p, q, P, hP, hSP⟩
      -- Reduce the forward direction to the flattened mixed-integer witness decomposition.
      exact unionRationalPolytopesAddIntegralIntcone_ofRepresentableWitness hSP
        (existsFlatMixedIntegerWitnessDecomposition hP)
  · intro hrepr
    -- Package the converse direction through the selector-lift witness built above.
    exact mixedIntegerLinearRepresentable_of_unionRationalPolytopesAddIntegralIntcone hrepr
