import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4.ch5_sec5_4_definition_5_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_2.ch10_sec10_2_2_theorem_10_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_3_theorem_10_10
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_7

open SimpleGraph
open scoped LovaszSchrijverNotation Matrix

noncomputable section

-- Domain sampling note:
-- * source-facing graph owners reused from Chapters 7 and 10.2:
--   `fractional_stable_set_polytope`, `clique_relaxation`, `stableSetPolytope`, `theta_body`
-- * source-facing owner reused from Chapter 5: `coordinate_lift_project_hull`
-- * core/canonical Section 10.3 owner reused directly: `lovasz_schrijver_N_plus`
-- This file keeps only the exercise-specific five-cycle statements.

section Exercise10_8

local notation "C₅" => cycleGraph 5

/-- Helper for Exercise 10.8: every clique of `C₅` has at most two vertices. -/
private lemma c5Clique_card_le_two
    (K : Finset (Fin 5)) (hK : (C₅).IsClique K) :
    K.card ≤ 2 := by
  -- The five-cycle is triangle-free, so a clique cannot have three vertices.
  revert hK K
  decide

/-- Helper for Exercise 10.8: every stable set of `C₅` has at most two vertices. -/
private lemma c5Indep_card_le_two
    (s : Finset (Fin 5)) (hs : (C₅).IsIndepSet s) :
    s.card ≤ 2 := by
  -- This is the finite-cycle combinatorics used in the odd-cycle inequality.
  revert hs s
  decide

/-- Helper for Exercise 10.8: the singleton stable-set vertex at `j` belongs to `STAB(C₅)`. -/
private lemma cycleSinglePoint_mem_stableSetPolytope (j : Fin 5) :
    (Pi.single j (1 : ℝ) : Fin 5 → ℝ) ∈ STAB(C₅) := by
  -- Realize the point as the indicator of the singleton stable set `{j}`.
  rw [stableSetPolytope_eq_convexHull]
  apply subset_convexHull
  rw [mem_stableSetVertices_iff]
  refine ⟨{j}, ?_, ?_⟩
  · revert j
    decide
  · ext i
    by_cases hi : i = j
    · subst hi
      simp [stableSetIndicator]
    · simp [stableSetIndicator, hi]

/-- Helper for Exercise 10.8: the distance-two stable pair of `C₅` gives a stable-set-polytope
vertex. -/
private lemma cycleTwoStepPairPoint_mem_stableSetPolytope (j : Fin 5) :
    (Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 j)) 1 : Fin 5 → ℝ) ∈ STAB(C₅) := by
  -- Realize the sparse vector as the indicator of the corresponding stable pair.
  rw [stableSetPolytope_eq_convexHull]
  apply subset_convexHull
  rw [mem_stableSetVertices_iff]
  refine ⟨{j, finRotate 5 (finRotate 5 j)}, ?_, ?_⟩
  · revert j
    decide
  · ext i
    fin_cases i <;> fin_cases j <;> simp [stableSetIndicator]

/-- Helper for Exercise 10.8: the distance-three stable pair of `C₅` gives a stable-set-polytope
vertex. -/
private lemma cycleThreeStepPairPoint_mem_stableSetPolytope (j : Fin 5) :
    (Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 (finRotate 5 j))) 1 :
        Fin 5 → ℝ) ∈ STAB(C₅) := by
  -- Realize the sparse vector as the indicator of the other stable pair through `j`.
  rw [stableSetPolytope_eq_convexHull]
  apply subset_convexHull
  rw [mem_stableSetVertices_iff]
  refine ⟨{j, finRotate 5 (finRotate 5 (finRotate 5 j))}, ?_, ?_⟩
  · revert j
    decide
  · ext i
    fin_cases i <;> fin_cases j <;> simp [stableSetIndicator]

/-- Helper for Exercise 10.8: every stable-set indicator of `C₅` satisfies the fractional
relaxation constraints. -/
private lemma stableSetIndicator_mem_fractionalStableSetPolytope
    {s : Finset (Fin 5)} (hs : (C₅).IsIndepSet s) :
    stableSetIndicator s ∈ FRAC(C₅) := by
  -- The indicator is binary and no cycle edge can meet the stable set twice.
  rw [mem_fractional_stable_set_polytope_iff]
  refine ⟨?_, ?_⟩
  · intro v
    by_cases hv : v ∈ s
    · simp [stableSetIndicator, hv]
    · simp [stableSetIndicator, hv]
  · intro u v huv
    by_cases hu : u ∈ s
    · by_cases hv : v ∈ s
      · exact False.elim ((hs hu hv huv.ne) huv)
      · simp [stableSetIndicator, hu, hv]
    · by_cases hv : v ∈ s
      · simp [stableSetIndicator, hu, hv]
      · simp [stableSetIndicator, hu, hv]

/-- Helper for Exercise 10.8: consecutive vertices of `C₅` are adjacent. -/
private lemma cycleAdj_rotate (j : Fin 5) :
    (C₅).Adj j (finRotate 5 j) := by
  revert j
  decide

/-- For the five-cycle `C₅`, the fractional stable-set relaxation `FRAC(C₅)` agrees with the
clique relaxation `QSTAB(C₅)` because every clique has size at most two. -/
theorem exercise_10_8_frac_relaxation_eq_clique_relaxation :
    FRAC(C₅) = QSTAB(C₅) := by
  -- Compare the clique system against the edge system using the fact that `C₅` has no triangles.
  ext x
  constructor
  · intro hx
    rw [mem_fractional_stable_set_polytope_iff] at hx
    rw [mem_clique_relaxation_iff]
    refine ⟨fun v ↦ (hx.1 v).1, ?_⟩
    intro K hK
    have hcard : K.card ≤ 2 := c5Clique_card_le_two K hK
    rcases Nat.eq_or_lt_of_le hcard with hcard2 | hlt2
    · rcases Finset.card_eq_two.mp hcard2 with ⟨u, v, huv, rfl⟩
      have huvAdj : (C₅).Adj u v := by
        have hu : u ∈ ({u, v} : Finset (Fin 5)) := by simp
        have hv : v ∈ ({u, v} : Finset (Fin 5)) := by simp
        exact hK hu hv huv
      simpa [huv, add_comm] using hx.2 huvAdj
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hlt2) with hcard1 | hcard0
      · rcases Finset.card_eq_one.mp hcard1 with ⟨v, rfl⟩
        simpa using (hx.1 v).2
      · have hKempty : K = ∅ := by
          apply Finset.card_eq_zero.mp
          omega
        simp [hKempty]
  · intro hx
    rw [mem_clique_relaxation_iff] at hx
    rw [mem_fractional_stable_set_polytope_iff]
    refine ⟨?_, ?_⟩
    · intro v
      refine ⟨hx.1 v, ?_⟩
      have hsingleton : (C₅).IsClique ({v} : Finset (Fin 5)) := by
        apply SimpleGraph.IsClique.of_subsingleton
        intro a ha b hb
        have ha' : a = v := by simpa using ha
        have hb' : b = v := by simpa using hb
        simp [ha', hb']
      simpa using hx.2 ({v} : Finset (Fin 5)) hsingleton
    · intro u v huv
      have hpairClique : (C₅).IsClique ({u, v} : Finset (Fin 5)) := by
        simpa [isClique_pair] using (show u ≠ v → (C₅).Adj u v from fun _ ↦ huv)
      simpa [Finset.sum_pair huv.ne, add_comm] using hx.2 ({u, v} : Finset (Fin 5)) hpairClique

/-- Helper for Exercise 10.8: the zero vector is the indicator of the empty stable set of `C₅`. -/
private lemma cycleZeroPoint_mem_stableSetPolytope :
    (0 : Fin 5 → ℝ) ∈ STAB(C₅) := by
  -- Realize the origin as the stable-set indicator of `∅`.
  rw [stableSetPolytope_eq_convexHull]
  apply subset_convexHull
  rw [mem_stableSetVertices_iff]
  refine ⟨∅, by simp, ?_⟩
  ext i
  simp [stableSetIndicator]

/-- Helper for Exercise 10.8: summing the coordinates of a stable-set indicator counts its
support. -/
private lemma sum_stableSetIndicator_eq_card (s : Finset (Fin 5)) :
    (∑ v : Fin 5, stableSetIndicator s v) = s.card := by
  classical
  -- Each selected coordinate contributes `1`, and each unselected coordinate contributes `0`.
  simp [stableSetIndicator]

/-- Helper for Exercise 10.8: any linear inequality that is valid on every stable-set indicator is
valid on `STAB(C₅)`. -/
private lemma dotProductLeOfMemStableSetPolytope
    {c : Fin 5 → ℝ} {δ : ℝ}
    (hvertex : ∀ s : Finset (Fin 5), (C₅).IsIndepSet s → c ⬝ᵥ stableSetIndicator s ≤ δ)
    {x : Fin 5 → ℝ} (hx : x ∈ STAB(C₅)) :
    c ⬝ᵥ x ≤ δ := by
  -- Route correction: push the linear inequality to the stable-set vertices, then transport it
  -- across the convex-hull description of `STAB(C₅)`.
  let S : Set (Fin 5 → ℝ) := {y | c ⬝ᵥ y ≤ δ}
  have hsubset : stableSetVertices C₅ ⊆ S := by
    intro y hy
    rw [mem_stableSetVertices_iff] at hy
    rcases hy with ⟨s, hs, rfl⟩
    exact hvertex s hs
  have hconv : Convex ℝ S := by
    let f : (Fin 5 → ℝ) →ₗ[ℝ] ℝ := (dotProductEquiv ℝ (Fin 5)) c
    have hpre : Convex ℝ (f ⁻¹' Set.Iic δ) := (convex_Iic δ).linear_preimage f
    simpa [S, f, dotProductEquiv_apply_apply] using hpre
  rw [stableSetPolytope_eq_convexHull] at hx
  exact convexHull_min hsubset hconv hx

/-- Helper for Exercise 10.8: every point of `STAB(C₅)` satisfies the odd-cycle inequality
`∑ i, x i ≤ 2`. -/
private lemma stableSetPolytope_sum_le_two
    {x : Fin 5 → ℝ} (hx : x ∈ STAB(C₅)) :
    ∑ i : Fin 5, x i ≤ 2 := by
  -- Apply the generic vertex-valid inequality transfer to the all-ones linear form.
  have hdot :
      (fun _ : Fin 5 ↦ (1 : ℝ)) ⬝ᵥ x ≤ 2 := by
    refine dotProductLeOfMemStableSetPolytope ?_ hx
    intro s hs
    have hsCard : (s.card : ℝ) ≤ 2 := by
      exact_mod_cast c5Indep_card_le_two s hs
    simpa [dotProduct, sum_stableSetIndicator_eq_card] using hsCard
  simpa [dotProduct] using hdot

/-- Helper for Exercise 10.8: `STAB(C₅)` is convex. -/
private lemma convex_stableSetPolytope :
    Convex ℝ (STAB(C₅)) := by
  -- The stable-set polytope is a convex hull by definition.
  simpa [stableSetPolytope_eq_convexHull] using
    (convex_convexHull ℝ (stableSetVertices C₅))

/-- Helper for Exercise 10.8: a finite convex combination of points already in `STAB(C₅)` stays
in `STAB(C₅)`. -/
private lemma mem_stableSetPolytope_of_exists_fintype
    {ι : Type*} [Fintype ι] {x : Fin 5 → ℝ}
    (w : ι → ℝ) (z : ι → Fin 5 → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    (hz : ∀ i, z i ∈ STAB(C₅))
    (hx : ∑ i, w i • z i = x) :
    x ∈ STAB(C₅) := by
  -- First place the explicit weighted sum in the convex hull of the chosen stable points.
  have hxHull : x ∈ convexHull ℝ (Set.range z) := by
    exact mem_convexHull_of_exists_fintype w z hw_nonneg hw_sum (fun i ↦ Set.mem_range_self i) hx
  -- Then contract that finite convex hull back into the ambient stable-set polytope.
  exact convexHull_min (fun y hy ↦ by
      rcases hy with ⟨i, rfl⟩
      exact hz i) convex_stableSetPolytope hxHull

/-- Helper for Exercise 10.8: the constant point with value `1 / Real.sqrt 5` on `C₅`. -/
private noncomputable def constantInvSqrtFiveValue : ℝ :=
  1 / Real.sqrt 5

/-- Helper for Exercise 10.8: the constant point with value `1 / Real.sqrt 5` on `C₅`. -/
private noncomputable def constantInvSqrtFive : Fin 5 → ℝ :=
  fun _ ↦ constantInvSqrtFiveValue

/-- Helper for Exercise 10.8: the `Option`-indexed Gram family used to witness
`constantInvSqrtFive ∈ TH(C₅)`. -/
private noncomputable def constantInvSqrtFiveWitnessVectors :
    Option (Fin 5) → EuclideanSpace ℝ (Fin 3)
  | none => WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ)
  | some i =>
      WithLp.toLp 2
        (![constantInvSqrtFiveValue,
          Real.sqrt (constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue)) *
            exercise_10_7_pentagonVectors i 0,
          Real.sqrt (constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue)) *
            exercise_10_7_pentagonVectors i 1] :
          Fin 3 → ℝ)

/-- Helper for Exercise 10.8: the scalar `1 / Real.sqrt 5` is positive. -/
private lemma constantInvSqrtFive_pos :
    0 < constantInvSqrtFiveValue := by
  -- Positivity of `sqrt 5` makes its reciprocal positive.
  have hsqrt_pos : 0 < Real.sqrt 5 := by
    exact Real.sqrt_pos.2 (by positivity)
  unfold constantInvSqrtFiveValue
  exact one_div_pos.mpr hsqrt_pos

/-- Helper for Exercise 10.8: the scalar `1 / Real.sqrt 5` lies in `[0, 1]`. -/
private lemma constantInvSqrtFive_le_one :
    constantInvSqrtFiveValue ≤ 1 := by
  -- Compare the reciprocal with `1` using `Real.sqrt 5 > 1`.
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  have hsqrt_gt_one : 1 < Real.sqrt 5 := by
    nlinarith [hsqrt_sq, Real.sqrt_nonneg 5]
  have hsqrt_pos : 0 < Real.sqrt 5 := by
    exact Real.sqrt_pos.2 (by positivity)
  unfold constantInvSqrtFiveValue
  field_simp [hsqrt_pos.ne']
  nlinarith

/-- Helper for Exercise 10.8: the diagonal scalar identity for the local `1 / √5` witness. -/
private lemma constantInvSqrtFive_diag :
    constantInvSqrtFiveValue ^ 2 +
      constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue) =
      constantInvSqrtFiveValue := by
  -- The radial term was chosen so that the diagonal adds back to the first coordinate.
  ring

/-- Helper for Exercise 10.8: the adjacent pentagon inner product cancels the `1 / √5`
witness value to `0`. -/
private lemma constantInvSqrtFive_edge :
    constantInvSqrtFiveValue ^ 2 +
      (constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue)) *
        (-(1 + Real.sqrt 5) / 4) = 0 := by
  -- This is the standard five-cycle cancellation `α + (1 - α) cos (4π/5) = 0`.
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  have hsqrt_pos : 0 < Real.sqrt 5 := by
    exact Real.sqrt_pos.2 (by positivity)
  simp [constantInvSqrtFiveValue]
  field_simp [hsqrt_pos.ne']
  nlinarith

/-- Helper for Exercise 10.8: the `some`-indexed witness vectors have an inner product controlled
by the Exercise 10.7 pentagon Gram matrix. -/
private lemma constantInvSqrtFiveWitnessVectors_some_inner (i j : Fin 5) :
    Matrix.gram ℝ constantInvSqrtFiveWitnessVectors (some i) (some j) =
      constantInvSqrtFiveValue ^ 2 +
        (constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue)) *
          Matrix.gram ℝ exercise_10_7_pentagonVectors i j := by
  -- Expand the `ℝ³` Gram entry and collapse the squared radial factor once.
  have hnonneg :
      0 ≤ constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue) := by
    exact mul_nonneg (le_of_lt constantInvSqrtFive_pos) (sub_nonneg.mpr constantInvSqrtFive_le_one)
  have hs :
      Real.sqrt (constantInvSqrtFiveValue - constantInvSqrtFiveValue ^ 2) ^ 2 =
        constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue) := by
    have hrewrite :
        constantInvSqrtFiveValue - constantInvSqrtFiveValue ^ 2 =
          constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue) := by
      ring
    rw [hrewrite]
    exact Real.sq_sqrt hnonneg
  simp [Matrix.gram_apply, constantInvSqrtFiveWitnessVectors, exercise_10_7_pentagonVectors,
    PiLp.inner_apply, Fin.sum_univ_three]
  ring_nf
  rw [hs]
  ring

/-- Helper for Exercise 10.8: the constant point `1 / √5` lies in `TH(C₅)`. -/
private lemma constantInvSqrtFive_mem_thetaBody :
    constantInvSqrtFive ∈ TH(C₅) := by
  -- Route correction: reuse the Example 10.6 Gram-witness skeleton with the Exercise 10.7 owner
  -- Gram data already imported in this file.
  let Y : Matrix (Option (Fin 5)) (Option (Fin 5)) ℝ :=
    Matrix.gram ℝ constantInvSqrtFiveWitnessVectors
  have hdiagPentagon (v : Fin 5) :
      Matrix.gram ℝ exercise_10_7_pentagonVectors v v = 1 := by
    -- The diagonal pentagon entry is the cosine at angle `0`.
    rw [exercise_10_7_gram_entry]
    simp
  refine ⟨Y, Matrix.IsThetaBodyWitness.mk (G := C₅) ?_ ?_ ?_ ?_ ?_⟩
  · -- The Gram matrix is automatically positive semidefinite.
    simpa [Y] using Matrix.posSemidef_gram ℝ constantInvSqrtFiveWitnessVectors
  · -- The `none, none` entry is the squared norm of `[1, 0, 0]`.
    change Matrix.gram ℝ constantInvSqrtFiveWitnessVectors none none = 1
    rw [Matrix.gram_apply]
    rw [inner_self_eq_norm_sq_to_K]
    change ‖WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ)‖ ^ 2 = 1
    have hvec : (![1, 0, 0] : Fin 3 → ℝ) = Pi.single (0 : Fin 3) (1 : ℝ) := by
      ext i
      fin_cases i <;> simp
    rw [hvec]
    change ‖PiLp.single 2 (β := fun _ : Fin 3 => ℝ) (0 : Fin 3) (1 : ℝ)‖ ^ 2 = 1
    rw [PiLp.norm_single]
    norm_num
  · intro v
    -- The `none` row recovers the constant vector `1 / √5`.
    change Matrix.gram ℝ constantInvSqrtFiveWitnessVectors none (some v) =
      constantInvSqrtFive v
    simp [constantInvSqrtFiveWitnessVectors, constantInvSqrtFive, Matrix.gram_apply,
      PiLp.inner_apply, Fin.sum_univ_three]
  · intro v
    -- The diagonal entry collapses to the scalar identity built into the witness.
    change Matrix.gram ℝ constantInvSqrtFiveWitnessVectors (some v) (some v) =
      constantInvSqrtFive v
    calc
      Matrix.gram ℝ constantInvSqrtFiveWitnessVectors (some v) (some v)
          = constantInvSqrtFiveValue ^ 2 +
              (constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue)) *
                Matrix.gram ℝ exercise_10_7_pentagonVectors v v := by
              exact constantInvSqrtFiveWitnessVectors_some_inner v v
      _ = constantInvSqrtFiveValue ^ 2 +
            (constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue)) * 1 := by
              rw [hdiagPentagon v]
      _ = constantInvSqrtFive v := by
              simpa [constantInvSqrtFive] using constantInvSqrtFive_diag
  · intro u v huv
    -- Adjacent entries cancel to `0` once the pentagon Gram entry is normalized.
    change Matrix.gram ℝ constantInvSqrtFiveWitnessVectors (some u) (some v) = 0
    have hPentagonGram :
        Matrix.gram ℝ exercise_10_7_pentagonVectors u v =
          exercise_10_7_witness u v := by
      simpa using congrArg (fun M ↦ M u v) exercise_10_7_witness_eq_gram.symm
    calc
      Matrix.gram ℝ constantInvSqrtFiveWitnessVectors (some u) (some v)
          = constantInvSqrtFiveValue ^ 2 +
              (constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue)) *
                Matrix.gram ℝ exercise_10_7_pentagonVectors u v := by
              exact constantInvSqrtFiveWitnessVectors_some_inner u v
      _ = constantInvSqrtFiveValue ^ 2 +
            (constantInvSqrtFiveValue * (1 - constantInvSqrtFiveValue)) *
              (-(1 + Real.sqrt 5) / 4) := by
              rw [hPentagonGram, exercise_10_7_witness_entry_of_adj huv]
      _ = 0 := constantInvSqrtFive_edge

/-- Helper for Exercise 10.8: the constant point `1 / √5` violates the odd-cycle inequality, so
it is not in `STAB(C₅)`. -/
private lemma constantInvSqrtFive_not_mem_stableSetPolytope :
    constantInvSqrtFive ∉ STAB(C₅) := by
  -- Compare the explicit coordinate sum `√5` against the odd-cycle inequality on `STAB(C₅)`.
  intro hx
  have hsum_le_two :
      ∑ i : Fin 5, constantInvSqrtFive i ≤ 2 := stableSetPolytope_sum_le_two hx
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  have hsqrt_pos : 0 < Real.sqrt 5 := by
    exact Real.sqrt_pos.2 (by positivity)
  have hsum_eq :
      ∑ i : Fin 5, constantInvSqrtFive i = Real.sqrt 5 := by
    simp [constantInvSqrtFive, constantInvSqrtFiveValue]
    field_simp [hsqrt_pos.ne']
    nlinarith
  have hsqrt_gt_two : 2 < Real.sqrt 5 := by
    nlinarith [hsqrt_sq, Real.sqrt_nonneg 5]
  rw [hsum_eq] at hsum_le_two
  linarith

/-- Helper for Exercise 10.8: the constant half-point on `C₅`. -/
private def halfPoint : Fin 5 → ℝ :=
  fun _ ↦ (1 / 2 : ℝ)

/-- Helper for Exercise 10.8: the constant half-point belongs to `QSTAB(C₅)`. -/
private lemma halfPoint_mem_clique_relaxation :
    halfPoint ∈ QSTAB(C₅) := by
  rw [← exercise_10_8_frac_relaxation_eq_clique_relaxation]
  rw [mem_fractional_stable_set_polytope_iff]
  refine ⟨?_, ?_⟩
  · intro v
    norm_num [halfPoint]
  · intro u v huv
    norm_num [halfPoint]

/-- Helper for Exercise 10.8: the constant half-point does not belong to `TH(C₅)`. -/
private lemma halfPoint_not_mem_thetaBody :
    halfPoint ∉ TH(C₅) := by
  intro hx
  rw [mem_theta_body_iff] at hx
  rcases hx with ⟨Y, hY⟩
  let χ : Fin 5 → ℝ := halfPoint
  have hZ : max_cut_sdp'_feasible χ Y := by
    -- Reuse the affine equalities of the theta-body witness as a lifted max-cut witness.
    refine max_cut_sdp'_feasible.mk ?_ ?_ ?_ ?_ ?_
    · exact Matrix.IsThetaBodyWitness.posSemidef (G := C₅) hY
    · exact Matrix.IsThetaBodyWitness.apply_none_none (G := C₅) hY
    · intro v
      exact Matrix.IsThetaBodyWitness.apply_none_some (G := C₅) hY v
    · intro v
      exact Matrix.IsThetaBodyWitness.apply_some_none (G := C₅) hY v
    · intro v
      exact Matrix.IsThetaBodyWitness.apply_some_some (G := C₅) hY v
  let B : Matrix (Fin 5) (Option (Fin 5)) ℝ := fun u i =>
    match i with
    | none => 1
    | some u' => if u' = u then -2 else 0
  let X : Matrix (Fin 5) (Fin 5) ℝ :=
    fun u v ↦ 1 - 2 * χ u - 2 * χ v + 4 * Y (some u) (some v)
  have hX : goemans_williamson_feasible X := by
    -- The Exercise 10.4 affine bridge turns the theta witness into a GW witness.
    refine goemans_williamson_feasible.mk ?_ ?_
    · have hXeq : X = B * Y * B.conjTranspose := by
        ext u v
        simpa [X, B, χ] using (liftedBridgeMatrix_apply (χ := χ) (Z := Y) hZ u v).symm
      rw [hXeq]
      exact (max_cut_sdp'_feasible.posSemidef hZ).mul_mul_conjTranspose_same B
    · intro v
      simp [X, χ, halfPoint, Matrix.IsThetaBodyWitness.apply_some_some (G := C₅) hY]
      ring
  have hXedge {u v : Fin 5} (huv : (C₅).Adj u v) : X u v = -1 := by
    -- On edges, the theta-body witness vanishes, so the bridge matrix yields `-1`.
    calc
      X u v = 1 - 2 * χ u - 2 * χ v + 4 * Y (some u) (some v) := rfl
      _ = 1 - 2 * (1 / 2 : ℝ) - 2 * (1 / 2 : ℝ) + 4 * 0 := by
            simp [
              χ,
              halfPoint,
              Matrix.IsThetaBodyWitness.apply_some_some_eq_zero_of_adj (G := C₅) hY huv
            ]
      _ = -1 := by ring
  have hplusZero {u v : Fin 5} (huv : (C₅).Adj u v) :
      X *ᵥ (Pi.single u (1 : ℝ) + Pi.single v 1) = 0 := by
    -- The PSD quadratic form vanishes on `e_u + e_v`, so the vector lies in the kernel.
    have hquad :
        (Pi.single u (1 : ℝ) + Pi.single v 1) ⬝ᵥ
            (X *ᵥ (Pi.single u (1 : ℝ) + Pi.single v 1)) = 0 := by
      rw [goemansWilliamsonEdgePlusEval (hX := hX) u v, hXedge huv, hXedge huv.symm]
      ring
    exact
      ((goemans_williamson_feasible.posSemidef hX).dotProduct_mulVec_zero_iff
        (Pi.single u (1 : ℝ) + Pi.single v 1)).1 <| by
          simpa using hquad
  have hrow {u v : Fin 5} (huv : (C₅).Adj u v) :
      X 0 u + X 0 v = 0 := by
    -- Read the `0`th coordinate of the kernel relation for `e_u + e_v`.
    have hvec := congrArg (fun z : Fin 5 → ℝ ↦ z 0) (hplusZero huv)
    simpa [Matrix.mulVec_add, Matrix.mulVec_single_one] using hvec
  have hdiag0 : X 0 0 = 1 := goemans_williamson_feasible.diag_eq_one hX 0
  have h01 : X 0 1 = -1 := by
    have h01sum : X 0 0 + X 0 1 = 0 := hrow (by decide : (C₅).Adj 0 1)
    nlinarith
  have h02 : X 0 2 = 1 := by
    have h12sum : X 0 1 + X 0 2 = 0 := hrow (by decide : (C₅).Adj 1 2)
    nlinarith
  have h03 : X 0 3 = -1 := by
    have h23sum : X 0 2 + X 0 3 = 0 := hrow (by decide : (C₅).Adj 2 3)
    nlinarith
  have h04 : X 0 4 = 1 := by
    have h34sum : X 0 3 + X 0 4 = 0 := hrow (by decide : (C₅).Adj 3 4)
    nlinarith
  have hdiag0' : X 0 0 = -1 := by
    have h40sum : X 0 4 + X 0 0 = 0 := hrow (by decide : (C₅).Adj 4 0)
    nlinarith
  linarith

/-- Helper for Exercise 10.8: if `x ∈ FRAC(C₅)` and `x j = 1`, then `x ∈ STAB(C₅)`. -/
private lemma fracFaceAtOne_subset_stableSetPolytope
    {j : Fin 5} {x : Fin 5 → ℝ}
    (hx : x ∈ FRAC(C₅)) (hxj : x j = 1) :
    x ∈ STAB(C₅) := by
  -- Route correction: normalize around the chosen vertex `j`, then package the face point as a
  -- triangle between the three stable vertices through `j`.
  rw [mem_fractional_stable_set_polytope_iff] at hx
  rcases hx with ⟨hx_box, hx_edge⟩
  let j1 : Fin 5 := finRotate 5 j
  let j2 : Fin 5 := finRotate 5 j1
  let j3 : Fin 5 := finRotate 5 j2
  let j4 : Fin 5 := finRotate 5 j3
  have hjj1 : (C₅).Adj j j1 := by
    dsimp [j1]
    exact cycleAdj_rotate j
  have hj4j : (C₅).Adj j4 j := by
    dsimp [j1, j2, j3, j4]
    fin_cases j <;> decide
  have hj2j3 : (C₅).Adj j2 j3 := by
    dsimp [j1, j2, j3]
    fin_cases j <;> decide
  have hxj1_zero : x j1 = 0 := by
    -- The edge inequality on `jj1` forces the clockwise neighbor to vanish.
    have hsum : x j + x j1 ≤ 1 := hx_edge hjj1
    have hnonneg : 0 ≤ x j1 := (hx_box j1).1
    linarith
  have hxj4_zero : x j4 = 0 := by
    -- The edge inequality on `j4j` forces the counterclockwise neighbor to vanish.
    have hsum : x j4 + x j ≤ 1 := hx_edge hj4j
    have hnonneg : 0 ≤ x j4 := (hx_box j4).1
    linarith
  have hxj2_nonneg : 0 ≤ x j2 := (hx_box j2).1
  have hxj3_nonneg : 0 ≤ x j3 := (hx_box j3).1
  have hxj2j3_le : x j2 + x j3 ≤ 1 := hx_edge hj2j3
  have hbase_nonneg : 0 ≤ 1 - x j2 - x j3 := by
    linarith
  -- The remaining coordinates lie in the triangle spanned by `e_j`, `e_j + e_{j+2}`,
  -- and `e_j + e_{j+3}`.
  refine mem_stableSetPolytope_of_exists_fintype
    (ι := Fin 3)
    (w := fun
      | 0 => 1 - x j2 - x j3
      | 1 => x j2
      | 2 => x j3)
    (z := fun
      | 0 => Pi.single j (1 : ℝ)
      | 1 => Pi.single j (1 : ℝ) + Pi.single j2 1
      | 2 => Pi.single j (1 : ℝ) + Pi.single j3 1)
    ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hbase_nonneg
    · exact hxj2_nonneg
    · exact hxj3_nonneg
  · rw [Fin.sum_univ_three]
    ring
  · intro i
    fin_cases i
    · exact cycleSinglePoint_mem_stableSetPolytope j
    · simpa [j1, j2] using cycleTwoStepPairPoint_mem_stableSetPolytope j
    · simpa [j1, j2, j3] using cycleThreeStepPairPoint_mem_stableSetPolytope j
  · -- Compare all five coordinates against the explicit barycentric formula.
    have hj1_ne_j : j1 ≠ j := by
      dsimp [j1]
      fin_cases j <;> decide
    have hj2_ne_j : j2 ≠ j := by
      dsimp [j1, j2]
      fin_cases j <;> decide
    have hj3_ne_j : j3 ≠ j := by
      dsimp [j1, j2, j3]
      fin_cases j <;> decide
    have hj4_ne_j : j4 ≠ j := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    have hj1_ne_j2 : j1 ≠ j2 := by
      dsimp [j1, j2]
      fin_cases j <;> decide
    have hj1_ne_j3 : j1 ≠ j3 := by
      dsimp [j1, j2, j3]
      fin_cases j <;> decide
    have hj2_ne_j3 : j2 ≠ j3 := by
      dsimp [j1, j2, j3]
      fin_cases j <;> decide
    have hj4_ne_j2 : j4 ≠ j2 := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    have hj4_ne_j3 : j4 ≠ j3 := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    ext i
    have hi_cases : i = j ∨ i = j1 ∨ i = j2 ∨ i = j3 ∨ i = j4 := by
      fin_cases i <;> fin_cases j <;> simp [j1, j2, j3, j4]
    rcases hi_cases with rfl | rfl | rfl | rfl | rfl
    · rw [Fin.sum_univ_three]
      simp [hj2_ne_j.symm, hj3_ne_j.symm]
      ring_nf
      exact hxj.symm
    · rw [Fin.sum_univ_three]
      simpa [Pi.single_apply, hj1_ne_j, hj1_ne_j2, hj1_ne_j3] using hxj1_zero.symm
    · rw [Fin.sum_univ_three]
      simp [hj2_ne_j, hj2_ne_j3]
    · rw [Fin.sum_univ_three]
      simp [hj3_ne_j, hj2_ne_j3]
    · rw [Fin.sum_univ_three]
      simpa [Pi.single_apply, hj4_ne_j, hj4_ne_j2, hj4_ne_j3] using hxj4_zero.symm

/-- Helper for Exercise 10.8: if `x ∈ FRAC(C₅)` and `x j = 0`, then `x ∈ STAB(C₅)`. -/
private lemma fracFaceAtZero_of_leftEndpointLeRightEndpoint
    {j : Fin 5} {x : Fin 5 → ℝ}
    (hx : x ∈ FRAC(C₅)) (hxj : x j = 0)
    (horder :
      x (finRotate 5 j) ≤
        x (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))))) :
    x ∈ STAB(C₅) := by
  -- Route correction: the failed one-shot zero-face formula was too rigid, so this branch uses
  -- the endpoint order `x j1 ≤ x j4` together with all three stable pairs on the path face.
  rw [mem_fractional_stable_set_polytope_iff] at hx
  rcases hx with ⟨hx_box, hx_edge⟩
  let j1 : Fin 5 := finRotate 5 j
  let j2 : Fin 5 := finRotate 5 j1
  let j3 : Fin 5 := finRotate 5 j2
  let j4 : Fin 5 := finRotate 5 j3
  have hj1j2 : (C₅).Adj j1 j2 := by
    dsimp [j2]
    exact cycleAdj_rotate j1
  have hj2j3 : (C₅).Adj j2 j3 := by
    dsimp [j3]
    exact cycleAdj_rotate j2
  have hj3j4 : (C₅).Adj j3 j4 := by
    dsimp [j4]
    exact cycleAdj_rotate j3
  have hxj1_nonneg : 0 ≤ x j1 := (hx_box j1).1
  have hxj2_nonneg : 0 ≤ x j2 := (hx_box j2).1
  have hxj3_nonneg : 0 ≤ x j3 := (hx_box j3).1
  have hxj4_nonneg : 0 ≤ x j4 := (hx_box j4).1
  have hxj1j2_le : x j1 + x j2 ≤ 1 := hx_edge hj1j2
  have hxj2j3_le : x j2 + x j3 ≤ 1 := hx_edge hj2j3
  have hxj3j4_le : x j3 + x j4 ≤ 1 := hx_edge hj3j4
  let a : ℝ := max 0 (x j1 + x j2 + x j3 - 1)
  let b : ℝ := x j1 - a
  let c : ℝ := max 0 (x j2 + x j3 + x j4 - 1)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact le_max_left _ _
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact le_max_left _ _
  have ha_le_j1 : a ≤ x j1 := by
    dsimp [a]
    refine max_le_iff.mpr ⟨hxj1_nonneg, ?_⟩
    linarith [hxj2j3_le]
  have ha_le_j3 : a ≤ x j3 := by
    dsimp [a]
    refine max_le_iff.mpr ⟨hxj3_nonneg, ?_⟩
    linarith [hxj1j2_le]
  have hc_le_j2 : c ≤ x j2 := by
    dsimp [c]
    refine max_le_iff.mpr ⟨hxj2_nonneg, ?_⟩
    linarith [hxj3j4_le]
  have h123_le_a : x j1 + x j2 + x j3 - 1 ≤ a := by
    dsimp [a]
    exact le_max_right _ _
  have hc_le_gap : c ≤ x j4 - x j1 + a := by
    dsimp [c]
    refine max_le_iff.mpr ⟨by linarith [horder, ha_nonneg], ?_⟩
    linarith [h123_le_a]
  have hb_nonneg : 0 ≤ b := by
    linarith
  have hbase_nonneg : 0 ≤ 1 - x j2 - x j3 - x j4 + c := by
    -- The zero-face remainder is exactly the positive part of `1 - x j2 - x j3 - x j4`.
    dsimp [c]
    by_cases hc_case : 0 ≤ x j2 + x j3 + x j4 - 1
    · rw [max_eq_right hc_case]
      nlinarith
    · have hc' : x j2 + x j3 + x j4 - 1 ≤ 0 := le_of_not_ge hc_case
      rw [max_eq_left hc']
      linarith
  -- Package the face point as a convex combination of `0`, three singletons, and three stable
  -- pairs. The last index is a dummy zero-weight term so we can reuse `Fin.sum_univ_eight`.
  refine mem_stableSetPolytope_of_exists_fintype
    (ι := Fin 8)
    (w := fun
      | 0 => 1 - x j2 - x j3 - x j4 + c
      | 1 => x j2 - c
      | 2 => x j3 - a
      | 3 => x j4 - x j1 + a - c
      | 4 => a
      | 5 => b
      | 6 => c
      | 7 => 0)
    (z := fun
      | 0 => 0
      | 1 => Pi.single j2 (1 : ℝ)
      | 2 => Pi.single j3 (1 : ℝ)
      | 3 => Pi.single j4 (1 : ℝ)
      | 4 => Pi.single j1 (1 : ℝ) + Pi.single j3 1
      | 5 => Pi.single j1 (1 : ℝ) + Pi.single j4 1
      | 6 => Pi.single j2 (1 : ℝ) + Pi.single j4 1
      | 7 => 0)
    ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hbase_nonneg
    · linarith
    · linarith
    · linarith
    · exact ha_nonneg
    · exact hb_nonneg
    · exact hc_nonneg
    · positivity
  · rw [Fin.sum_univ_eight]
    ring
  · intro i
    fin_cases i
    · exact cycleZeroPoint_mem_stableSetPolytope
    · exact cycleSinglePoint_mem_stableSetPolytope j2
    · exact cycleSinglePoint_mem_stableSetPolytope j3
    · exact cycleSinglePoint_mem_stableSetPolytope j4
    · simpa [j2, j3] using cycleTwoStepPairPoint_mem_stableSetPolytope j1
    · simpa [j2, j3, j4] using cycleThreeStepPairPoint_mem_stableSetPolytope j1
    · simpa [j3, j4] using cycleTwoStepPairPoint_mem_stableSetPolytope j2
    · exact cycleZeroPoint_mem_stableSetPolytope
  · -- The corrected barycentric formula recovers each coordinate of `x`.
    ext i
    have hj1_ne_j : j1 ≠ j := by
      dsimp [j1]
      fin_cases j <;> decide
    have hj2_ne_j : j2 ≠ j := by
      dsimp [j1, j2]
      fin_cases j <;> decide
    have hj3_ne_j : j3 ≠ j := by
      dsimp [j1, j2, j3]
      fin_cases j <;> decide
    have hj4_ne_j : j4 ≠ j := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    have hj1_ne_j2 : j1 ≠ j2 := by
      dsimp [j1, j2]
      fin_cases j <;> decide
    have hj1_ne_j3 : j1 ≠ j3 := by
      dsimp [j1, j2, j3]
      fin_cases j <;> decide
    have hj1_ne_j4 : j1 ≠ j4 := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    have hj2_ne_j3 : j2 ≠ j3 := by
      dsimp [j1, j2, j3]
      fin_cases j <;> decide
    have hj2_ne_j4 : j2 ≠ j4 := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    have hj3_ne_j4 : j3 ≠ j4 := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    have hi_cases : i = j ∨ i = j1 ∨ i = j2 ∨ i = j3 ∨ i = j4 := by
      fin_cases i <;> fin_cases j <;> simp [j1, j2, j3, j4]
    rcases hi_cases with rfl | rfl | rfl | rfl | rfl
    · rw [Fin.sum_univ_eight]
      simpa [hj1_ne_j, hj2_ne_j, hj3_ne_j, hj4_ne_j] using hxj.symm
    · rw [Fin.sum_univ_eight]
      simp [hj1_ne_j2, hj1_ne_j3, hj1_ne_j4]
      dsimp [b]
      ring
    · rw [Fin.sum_univ_eight]
      simp [hj1_ne_j2, hj2_ne_j3, hj2_ne_j4]
    · rw [Fin.sum_univ_eight]
      simp [hj1_ne_j3, hj2_ne_j3, hj3_ne_j4, b]
    · rw [Fin.sum_univ_eight]
      simp [hj1_ne_j4, hj2_ne_j4, hj3_ne_j4]
      dsimp [b]
      ring

/-- Helper for Exercise 10.8: the symmetric zero-face branch also lies in `STAB(C₅)`. -/
private lemma fracFaceAtZero_of_rightEndpointLeLeftEndpoint
    {j : Fin 5} {x : Fin 5 → ℝ}
    (hx : x ∈ FRAC(C₅)) (hxj : x j = 0)
    (horder :
      x (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j)))) ≤ x (finRotate 5 j)) :
    x ∈ STAB(C₅) := by
  -- Route correction: this is the symmetric endpoint-order branch, again using all three path
  -- stable pairs instead of a brittle two-pair normal form.
  rw [mem_fractional_stable_set_polytope_iff] at hx
  rcases hx with ⟨hx_box, hx_edge⟩
  let j1 : Fin 5 := finRotate 5 j
  let j2 : Fin 5 := finRotate 5 j1
  let j3 : Fin 5 := finRotate 5 j2
  let j4 : Fin 5 := finRotate 5 j3
  have hj1j2 : (C₅).Adj j1 j2 := by
    dsimp [j2]
    exact cycleAdj_rotate j1
  have hj2j3 : (C₅).Adj j2 j3 := by
    dsimp [j3]
    exact cycleAdj_rotate j2
  have hj3j4 : (C₅).Adj j3 j4 := by
    dsimp [j4]
    exact cycleAdj_rotate j3
  have hxj1_nonneg : 0 ≤ x j1 := (hx_box j1).1
  have hxj2_nonneg : 0 ≤ x j2 := (hx_box j2).1
  have hxj3_nonneg : 0 ≤ x j3 := (hx_box j3).1
  have hxj4_nonneg : 0 ≤ x j4 := (hx_box j4).1
  have hxj1j2_le : x j1 + x j2 ≤ 1 := hx_edge hj1j2
  have hxj2j3_le : x j2 + x j3 ≤ 1 := hx_edge hj2j3
  have hxj3j4_le : x j3 + x j4 ≤ 1 := hx_edge hj3j4
  let a : ℝ := max 0 (x j2 + x j3 + x j4 - 1)
  let b : ℝ := x j4 - a
  let c : ℝ := max 0 (x j1 + x j2 + x j3 - 1)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact le_max_left _ _
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact le_max_left _ _
  have ha_le_j4 : a ≤ x j4 := by
    dsimp [a]
    refine max_le_iff.mpr ⟨hxj4_nonneg, ?_⟩
    linarith [hxj2j3_le]
  have ha_le_j2 : a ≤ x j2 := by
    dsimp [a]
    refine max_le_iff.mpr ⟨hxj2_nonneg, ?_⟩
    linarith [hxj3j4_le]
  have hc_le_j3 : c ≤ x j3 := by
    dsimp [c]
    refine max_le_iff.mpr ⟨hxj3_nonneg, ?_⟩
    linarith [hxj1j2_le]
  have h234_le_a : x j2 + x j3 + x j4 - 1 ≤ a := by
    dsimp [a]
    exact le_max_right _ _
  have hc_le_gap : c ≤ x j1 - x j4 + a := by
    dsimp [c]
    refine max_le_iff.mpr ⟨by linarith [horder, ha_nonneg], ?_⟩
    linarith [h234_le_a]
  have hb_nonneg : 0 ≤ b := by
    linarith
  have hbase_nonneg : 0 ≤ 1 - x j1 - x j2 - x j3 + c := by
    -- The remaining zero-face weight is the positive part of `1 - x j1 - x j2 - x j3`.
    dsimp [c]
    by_cases hc_case : 0 ≤ x j1 + x j2 + x j3 - 1
    · rw [max_eq_right hc_case]
      nlinarith
    · have hc' : x j1 + x j2 + x j3 - 1 ≤ 0 := le_of_not_ge hc_case
      rw [max_eq_left hc']
      linarith
  -- The symmetric branch uses the same three stable pairs, but centered at the other endpoint.
  refine mem_stableSetPolytope_of_exists_fintype
    (ι := Fin 8)
    (w := fun
      | 0 => 1 - x j1 - x j2 - x j3 + c
      | 1 => x j1 - x j4 + a - c
      | 2 => x j2 - a
      | 3 => x j3 - c
      | 4 => a
      | 5 => b
      | 6 => c
      | 7 => 0)
    (z := fun
      | 0 => 0
      | 1 => Pi.single j1 (1 : ℝ)
      | 2 => Pi.single j2 (1 : ℝ)
      | 3 => Pi.single j3 (1 : ℝ)
      | 4 => Pi.single j2 (1 : ℝ) + Pi.single j4 1
      | 5 => Pi.single j1 (1 : ℝ) + Pi.single j4 1
      | 6 => Pi.single j1 (1 : ℝ) + Pi.single j3 1
      | 7 => 0)
    ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hbase_nonneg
    · linarith
    · linarith
    · linarith
    · exact ha_nonneg
    · exact hb_nonneg
    · exact hc_nonneg
    · positivity
  · rw [Fin.sum_univ_eight]
    ring
  · intro i
    fin_cases i
    · exact cycleZeroPoint_mem_stableSetPolytope
    · exact cycleSinglePoint_mem_stableSetPolytope j1
    · exact cycleSinglePoint_mem_stableSetPolytope j2
    · exact cycleSinglePoint_mem_stableSetPolytope j3
    · simpa [j3, j4] using cycleTwoStepPairPoint_mem_stableSetPolytope j2
    · simpa [j2, j3, j4] using cycleThreeStepPairPoint_mem_stableSetPolytope j1
    · simpa [j2, j3] using cycleTwoStepPairPoint_mem_stableSetPolytope j1
    · exact cycleZeroPoint_mem_stableSetPolytope
  · -- The symmetric barycentric formula again matches the original coordinates.
    ext i
    have hj1_ne_j : j1 ≠ j := by
      dsimp [j1]
      fin_cases j <;> decide
    have hj2_ne_j : j2 ≠ j := by
      dsimp [j1, j2]
      fin_cases j <;> decide
    have hj3_ne_j : j3 ≠ j := by
      dsimp [j1, j2, j3]
      fin_cases j <;> decide
    have hj4_ne_j : j4 ≠ j := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    have hj1_ne_j2 : j1 ≠ j2 := by
      dsimp [j1, j2]
      fin_cases j <;> decide
    have hj1_ne_j3 : j1 ≠ j3 := by
      dsimp [j1, j2, j3]
      fin_cases j <;> decide
    have hj1_ne_j4 : j1 ≠ j4 := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    have hj2_ne_j3 : j2 ≠ j3 := by
      dsimp [j1, j2, j3]
      fin_cases j <;> decide
    have hj2_ne_j4 : j2 ≠ j4 := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    have hj3_ne_j4 : j3 ≠ j4 := by
      dsimp [j1, j2, j3, j4]
      fin_cases j <;> decide
    have hi_cases : i = j ∨ i = j1 ∨ i = j2 ∨ i = j3 ∨ i = j4 := by
      fin_cases i <;> fin_cases j <;> simp [j1, j2, j3, j4]
    rcases hi_cases with rfl | rfl | rfl | rfl | rfl
    · rw [Fin.sum_univ_eight]
      simpa [hj1_ne_j, hj2_ne_j, hj3_ne_j, hj4_ne_j] using hxj.symm
    · rw [Fin.sum_univ_eight]
      simp [hj1_ne_j2, hj1_ne_j3, hj1_ne_j4]
      dsimp [b]
      ring
    · rw [Fin.sum_univ_eight]
      simp [hj1_ne_j2, hj2_ne_j3, hj2_ne_j4]
    · rw [Fin.sum_univ_eight]
      simp [hj1_ne_j3, hj2_ne_j3, hj3_ne_j4, b]
    · rw [Fin.sum_univ_eight]
      simp [hj1_ne_j4, hj2_ne_j4, hj3_ne_j4, b]

/-- Helper for Exercise 10.8: if `x ∈ FRAC(C₅)` and `x j = 0`, then `x ∈ STAB(C₅)`. -/
private lemma fracFaceAtZero_subset_stableSetPolytope
    {j : Fin 5} {x : Fin 5 → ℝ}
    (hx : x ∈ FRAC(C₅)) (hxj : x j = 0) :
    x ∈ STAB(C₅) := by
  let j1 : Fin 5 := finRotate 5 j
  let j2 : Fin 5 := finRotate 5 j1
  let j3 : Fin 5 := finRotate 5 j2
  let j4 : Fin 5 := finRotate 5 j3
  -- Route correction: split the zero face by the endpoint order and dispatch to the matching
  -- branchwise path-face decomposition.
  rcases le_total (x j1) (x j4) with hleft | hright
  · exact fracFaceAtZero_of_leftEndpointLeRightEndpoint hx hxj
      (by simpa [j1, j2, j3, j4] using hleft)
  · exact fracFaceAtZero_of_rightEndpointLeLeftEndpoint hx hxj
      (by simpa [j1, j2, j3, j4] using hright)

/-- Helper for Exercise 10.8: every stable-set indicator already lies in the coordinate
lift-project hull of `FRAC(C₅)`. -/
private lemma stableSetIndicator_mem_coordinateLiftProjectHull
    (j : Fin 5) {s : Finset (Fin 5)} (hs : (C₅).IsIndepSet s) :
    stableSetIndicator s ∈ coordinate_lift_project_hull (FRAC(C₅)) j := by
  -- Place the indicator in the `x j = 0` or `x j = 1` face according to membership of `j`.
  rw [coordinate_lift_project_hull_def]
  apply subset_convexHull
  by_cases hj : j ∈ s
  · right
    refine ⟨stableSetIndicator_mem_fractionalStableSetPolytope hs, ?_⟩
    simp [stableSetIndicator, hj]
  · left
    refine ⟨stableSetIndicator_mem_fractionalStableSetPolytope hs, ?_⟩
    simp [stableSetIndicator, hj]

/-- First strict inclusion for Exercise 10.8: for the five-cycle `C₅`, the inclusion
`STAB(C₅) ⊆ TH(C₅)` is strict. -/
theorem exercise_10_8_stableSetPolytope_ssubset_theta_body :
    STAB(C₅) ⊂ TH(C₅) := by
  -- Combine the owner inclusion `STAB ⊆ TH` with the explicit `1 / √5` witness outside `STAB`.
  rw [Set.ssubset_def]
  refine ⟨stableSetPolytope_subset_theta_body (G := C₅), ?_⟩
  intro hsubset
  exact constantInvSqrtFive_not_mem_stableSetPolytope
    (hsubset constantInvSqrtFive_mem_thetaBody)

/-- Second strict inclusion for Exercise 10.8: for the five-cycle `C₅`, the inclusion
`TH(C₅) ⊆ QSTAB(C₅)` is strict. -/
theorem exercise_10_8_theta_body_ssubset_clique_relaxation :
    TH(C₅) ⊂ QSTAB(C₅) := by
  rw [Set.ssubset_def]
  -- The half-point lies in `QSTAB(C₅)` but the odd-cycle PSD argument excludes it from `TH(C₅)`.
  refine ⟨theta_body_subset_clique_relaxation (G := C₅), ?_⟩
  intro hsubset
  exact halfPoint_not_mem_thetaBody (hsubset halfPoint_mem_clique_relaxation)

/-- Exercise 10.8 (3). For every coordinate `j = 1, ..., 5`, the lift-and-project set `P_j`
obtained from `P := FRAC(C₅)` is exactly `STAB(C₅)`. -/
theorem exercise_10_8_coordinate_lift_project_hull_eq_stableSetPolytope
    (j : Fin 5) :
    coordinate_lift_project_hull (FRAC(C₅)) j = STAB(C₅) := by
  -- Combine the two coordinate-face inclusions, then recover `STAB(C₅)` from its stable vertices.
  apply Set.Subset.antisymm
  · intro x hx
    rw [coordinate_lift_project_hull_def] at hx
    exact convexHull_min
      (by
        intro y hy
        rcases hy with ⟨hyFrac, hy0⟩ | ⟨hyFrac, hy1⟩
        · exact fracFaceAtZero_subset_stableSetPolytope hyFrac hy0
        · exact fracFaceAtOne_subset_stableSetPolytope hyFrac hy1)
      convex_stableSetPolytope hx
  · intro x hx
    rw [stableSetPolytope_eq_convexHull] at hx
    have hsubset :
        stableSetVertices C₅ ⊆ coordinate_lift_project_hull (FRAC(C₅)) j := by
      intro y hy
      rw [mem_stableSetVertices_iff] at hy
      rcases hy with ⟨s, hs, rfl⟩
      exact stableSetIndicator_mem_coordinateLiftProjectHull j hs
    have hconv :
        Convex ℝ (coordinate_lift_project_hull (FRAC(C₅)) j) := by
      rw [coordinate_lift_project_hull_def]
      exact convex_convexHull ℝ _
    exact convexHull_min hsubset hconv hx

/-- Helper for Exercise 10.8: every `N₊(FRAC(C₅))` point already lies in `STAB(C₅)`. -/
private lemma lovaszSchrijverNPlus_subset_stableSetPolytope :
    N₊(FRAC(C₅)) ⊆ STAB(C₅) := by
  -- Factor `N₊` through `N`, then through the coordinate lift-and-project hull at `j = 0`.
  have hFracBox : FRAC(C₅) ⊆ prefix_unit_box (Nat.le_refl 5) := by
    intro x hx
    rw [mem_prefix_unit_box_iff]
    rw [mem_fractional_stable_set_polytope_iff] at hx
    exact hx.1
  intro x hx
  have hxN : x ∈ N(FRAC(C₅)) := lovasz_schrijver_N_plus_subset_N (FRAC(C₅)) hx
  have hxCoord : x ∈ coordinate_lift_project_hull (FRAC(C₅)) 0 :=
    lovasz_schrijver_N_subset_coordinate_lift_project_hull (P := FRAC(C₅)) hFracBox 0 hxN
  rw [exercise_10_8_coordinate_lift_project_hull_eq_stableSetPolytope 0] at hxCoord
  exact hxCoord

/-- Final strict inclusion for Exercise 10.8: for the five-cycle `C₅`, the inclusion
`N₊(FRAC(C₅)) ⊆ TH(C₅)` is strict. -/
theorem exercise_10_8_lovasz_schrijver_N_plus_ssubset_theta_body :
    N₊(FRAC(C₅)) ⊂ TH(C₅) := by
  -- Factor `N₊(FRAC(C₅))` through `STAB(C₅)` and reuse the strict theta-body witness `1 / √5`.
  rw [Set.ssubset_def]
  refine ⟨Set.Subset.trans lovaszSchrijverNPlus_subset_stableSetPolytope
    (stableSetPolytope_subset_theta_body (G := C₅)), ?_⟩
  intro hsubset
  have hmemNplus : constantInvSqrtFive ∈ N₊(FRAC(C₅)) :=
    hsubset constantInvSqrtFive_mem_thetaBody
  exact constantInvSqrtFive_not_mem_stableSetPolytope
    (lovaszSchrijverNPlus_subset_stableSetPolytope hmemNplus)

end Exercise10_8
