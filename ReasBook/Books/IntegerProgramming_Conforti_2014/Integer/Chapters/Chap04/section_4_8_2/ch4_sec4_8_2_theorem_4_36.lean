import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_2.ch4_sec4_8_2_lemma_4_35
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_theorem_1_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_3

-- Domain-style sampling for this refine pass:
-- * primary domain: mixed-integer feasibility and certificate-size bounds
--   for rational mixed systems
-- * sampled declarations: `mixed_integer_points`, `mem_mixed_integer_points_iff`,
--   `nonnegative_rational_mixed_integer_points`, and the downstream hull surface in Lemma 4.38
-- * owner abstraction: the source-facing feasible-set owner
--   `nonnegative_rational_mixed_integer_points A G b`
-- * primitive data: rational system data `A`, `G`, `b`
--   with an entrywise encoding bound `L`
-- * derived API: a feasible mixed-integer witness with polynomially bounded encoding size

section Theorem436

variable {m n p : ℕ}

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_theorem_4_36.lean:
the convex hull of the nonnegative mixed-integer points remains coordinatewise nonnegative. -/
private lemma nonnegativeMixedIntegerHull_nonnegative
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ}
    {xy : MixedRealPoint n p}
    (hxy : xy ∈ convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)) :
    0 ≤ xy.1 ∧ 0 ≤ xy.2 := by
  -- First place every generating mixed-integer point in the product nonnegative orthant.
  have horthant :
      xy ∈ {uv : MixedRealPoint n p | 0 ≤ uv.1 ∧ 0 ≤ uv.2} := by
    refine convexHull_min ?_ ?_ hxy
    · intro uv huv
      have huvPoly := (mem_mixed_integer_points_iff.mp huv).1
      exact ⟨huvPoly.2.1, huvPoly.2.2⟩
    · intro u hu v hv a c ha hc hac
      -- Coordinatewise nonnegativity is preserved by convex combinations.
      constructor
      · intro i
        exact add_nonneg (smul_nonneg ha (hu.1 i)) (smul_nonneg hc (hv.1 i))
      · intro j
        exact add_nonneg (smul_nonneg ha (hu.2 j)) (smul_nonneg hc (hv.2 j))
  exact horthant

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_theorem_4_36.lean:
a nonempty subset of a finite-dimensional nonnegative orthant is pointed. -/
private lemma isPointed_of_nonempty_of_nonnegative
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP_nonempty : P.Nonempty)
    (hP_nonnegative : ∀ u ∈ P, 0 ≤ u) :
    is_pointed P := by
  -- A lineality direction may translate a fixed feasible point by every real scalar.
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro r hr
  rcases hP_nonempty with ⟨u, hu⟩
  funext i
  by_contra hri
  have hri' : r i ≠ 0 := by simpa using hri
  have htranslated :=
    (mem_linealitySpace_iff.mp hr) hu (-((u i + 1) / r i))
  have hnonnegative := hP_nonnegative _ htranslated i
  -- Choose the scalar that makes the selected coordinate equal to `-1`.
  have hcoord :
      (u + (-((u i + 1) / r i)) • r) i = -1 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hri']
    ring
  rw [hcoord] at hnonnegative
  norm_num at hnonnegative

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_theorem_4_36.lean:
the canonical block-concatenation equivalence used to flatten the mixed hull. -/
private abbrev nonnegativeMixedHullFlattening (n p : ℕ) :
    MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
  (Fin.appendEquiv n p).toLinearEquiv
    (Theorem15Support.isLinearMap_appendEquiv (n := n) (p := p))

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_theorem_4_36.lean:
the mixed-hull flattening acts as coordinate concatenation. -/
private lemma nonnegativeMixedHullFlattening_apply (xy : MixedRealPoint n p) :
    nonnegativeMixedHullFlattening n p xy = Fin.appendEquiv n p xy := by
  -- Expose the computation rule once, rather than unfolding the bundled equivalence at each use.
  rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_theorem_4_36.lean:
the nonempty nonnegative rational mixed-integer hull has an extreme point. -/
private lemma nonnegativeMixedIntegerHull_extremePoints_nonempty
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ)
    (hfeasible : Set.Nonempty (nonnegative_rational_mixed_integer_points A G b)) :
    Set.Nonempty
      ((convexHull ℝ
        (nonnegative_rational_mixed_integer_points A G b)).extremePoints ℝ) := by
  let H := convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)
  let e := nonnegativeMixedHullFlattening n p
  -- Theorem 1.5 supplies a rational presentation of the flattened hull.
  have hflatRational : is_rational_polyhedron (e '' H) := by
    simpa [H, e, is_rational_mixed_polyhedron, nonnegativeMixedHullFlattening] using
      (nonnegative_rational_mixed_integer_hull_is_rational_mixed_polyhedron A G b)
  have hflatPolyhedron : is_polyhedron (e '' H) := by
    rcases hflatRational with ⟨q, M, c, hpresentation⟩
    exact ⟨q, M.map (Rat.castHom ℝ), fun i ↦ (c i : ℝ), hpresentation⟩
  have hflatNonempty : Set.Nonempty (e '' H) := by
    rcases hfeasible with ⟨xy, hxy⟩
    exact ⟨e xy, xy, subset_convexHull ℝ _ hxy, rfl⟩
  have hflatNonnegative : ∀ u ∈ e '' H, 0 ≤ u := by
    rintro u ⟨xy, hxy, rfl⟩
    have hxyNonnegative := nonnegativeMixedIntegerHull_nonnegative hxy
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simpa [e, nonnegativeMixedHullFlattening_apply, Fin.appendEquiv] using
        hxyNonnegative.1 i
    · intro j
      simpa [e, nonnegativeMixedHullFlattening_apply, Fin.appendEquiv] using
        hxyNonnegative.2 j
  have hflatPointed : is_pointed (e '' H) :=
    isPointed_of_nonempty_of_nonnegative hflatNonempty hflatNonnegative
  -- A nonempty pointed polyhedron has a vertex; linear equivalence transports it back to `H`.
  obtain ⟨u, hu⟩ :=
    (polyhedron_extremePoints_nonempty_iff_is_pointed
      hflatPolyhedron hflatNonempty).2 hflatPointed
  rw [← image_extremePoints e H] at hu
  rcases hu with ⟨xy, hxy, _⟩
  exact ⟨xy, hxy⟩

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_theorem_4_36.lean — Theorem 4.36.
The MILP feasibility problem is in NP: for every feasible nonnegative rational mixed-integer
system whose coefficients have encoding size at most `L`, there is a certificate point with
integral `x`-block and rational `y`-block whose total encoding size is uniformly bounded by a
polynomial in `n + p + L`. -/
theorem mixed_integer_linear_feasibility_has_polynomially_bounded_certificate :
    ∃ π : Polynomial ℕ,
      ∀ {m n p : ℕ}
        (A : Matrix (Fin m) (Fin n) ℚ)
        (G : Matrix (Fin m) (Fin p) ℚ)
        (b : Fin m → ℚ)
        (L : ℕ)
        (hA : ∀ i : Fin m, ∀ j : Fin n, EncodingSize.rational (A i j) ≤ L)
        (hG : ∀ i : Fin m, ∀ j : Fin p, EncodingSize.rational (G i j) ≤ L)
        (hb : ∀ i : Fin m, EncodingSize.rational (b i) ≤ L)
        (hfeasible : Set.Nonempty (nonnegative_rational_mixed_integer_points A G b)),
        ∃ x : Fin n → ℤ,
          ∃ y : Fin p → ℚ,
            ((fun i ↦ (x i : ℝ)), fun j ↦ (y j : ℝ)) ∈
                nonnegative_rational_mixed_integer_points A G b ∧
              EncodingSize.integerVector x + EncodingSize.rationalVector y ≤
                π.eval (n + p + L) := by
  obtain ⟨π, hπ⟩ :=
    mixed_integer_hull_extreme_points_have_polynomially_bounded_encoding_size
  refine ⟨π, ?_⟩
  intro m n p A G b L hA hG hb hfeasible
  -- Choose a hull vertex and apply the uniform certificate bound from Lemma 4.35.
  obtain ⟨xy, hxy⟩ :=
    nonnegativeMixedIntegerHull_extremePoints_nonempty A G b hfeasible
  obtain ⟨x, y, hxyRepresentation, hsize⟩ :=
    hπ A G b L hA hG hb xy hxy
  refine ⟨x, y, ?_, hsize⟩
  -- Extremality places `xy` in the original feasible set, and its representation is the result.
  have hxyFeasible : xy ∈ nonnegative_rational_mixed_integer_points A G b :=
    extremePoints_convexHull_subset hxy
  simpa only [hxyRepresentation] using hxyFeasible

end Theorem436

#print axioms mixed_integer_linear_feasibility_has_polynomially_bounded_certificate
