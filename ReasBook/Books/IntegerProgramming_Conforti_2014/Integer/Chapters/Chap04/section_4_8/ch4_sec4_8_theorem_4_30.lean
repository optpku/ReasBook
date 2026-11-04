/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_13.ch3_sec3_13_theorem_3_39
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_4.ch3_sec3_4_4_definition_3_4_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_definition_3_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_corollary_4_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix Pointwise

-- Semantic recall note: the mixed-space owner API for rational mixed polyhedra and mixed-integer
-- points is already established upstream in Chapter 4.1, and the recession-cone owner is already
-- established generically in Chapter 3.6. This file therefore reuses those canonical surfaces
-- and adds only Theorem 4.30 and its thin source-facing bridge.

section Theorem430

variable {n p : ℕ}

/-- Helper for Theorem 4.30: flattening by `Fin.appendEquiv` rewrites mixed-integer membership as
membership in the flattened ambient set together with integrality of the first block. -/
lemma mem_flattened_mixed_integer_points_iff
    {P : Set (MixedRealPoint n p)}
    {u : Fin (n + p) → ℝ} :
    u ∈ (Fin.appendEquiv n p '' mixed_integer_points P) ↔
      u ∈ (Fin.appendEquiv n p '' P) ∧
        (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    -- Unpack mixed-integer membership into ambient membership and integrality of the `x`-block.
    rcases (mem_mixed_integer_points_iff).1 hxy with ⟨hP, hxy_lattice⟩
    constructor
    · exact ⟨xy, hP, rfl⟩
    · rw [mem_mixed_integer_lattice_iff] at hxy_lattice
      simpa using hxy_lattice
  · rintro ⟨huP, hu_int⟩
    rcases huP with ⟨xy, hxyP, rfl⟩
    -- The flattened integrality condition is exactly the mixed-lattice condition on `xy`.
    refine ⟨xy, ?_, rfl⟩
    refine (mem_mixed_integer_points_iff).2 ⟨hxyP, ?_⟩
    rw [mem_mixed_integer_lattice_iff]
    simpa using hu_int

/-- Helper for Theorem 4.30: mixed-integer points are contained in the ambient mixed polyhedron. -/
lemma mixed_integer_points_subset
    {P : Set (MixedRealPoint n p)} :
    mixed_integer_points P ⊆ P := by
  intro xy hxy
  -- The mixed-integer set is defined as `P ∩ (ℤ^n × ℝ^p)`.
  exact (mem_mixed_integer_points_iff).1 hxy |>.1

/-- Helper for Theorem 4.30: nonemptiness of the mixed-integer set gives a feasible base point of
the ambient mixed polyhedron. -/
lemma nonempty_of_mixed_integer_points_nonempty
    {P : Set (MixedRealPoint n p)}
    (hS_nonempty : Set.Nonempty (mixed_integer_points P)) :
    Set.Nonempty P := by
  rcases hS_nonempty with ⟨xy, hxy⟩
  -- Forgetting the integrality side condition leaves a point of `P`.
  exact ⟨xy, mixed_integer_points_subset hxy⟩

/-- Helper for Theorem 4.30: a nonempty mixed-integer set has nonempty convex hull. -/
lemma convexHull_mixed_integer_points_nonempty
    {P : Set (MixedRealPoint n p)}
    (hS_nonempty : Set.Nonempty (mixed_integer_points P)) :
    Set.Nonempty (convexHull ℝ (mixed_integer_points P)) := by
  -- The convex hull contains the original set.
  rcases hS_nonempty with ⟨xy, hxy⟩
  exact ⟨xy, subset_convexHull ℝ (mixed_integer_points P) hxy⟩

/-- Helper for Theorem 4.30: flattening by `Fin.appendEquiv` is linear on the mixed ambient
space. -/
lemma isLinearMap_appendEquiv :
    IsLinearMap ℝ (Fin.appendEquiv (α := ℝ) n p) := by
  refine ⟨?_, ?_⟩
  · intro x y
    -- Check the two coordinate blocks separately.
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]
  · intro a x
    -- Scalar multiplication is again blockwise.
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]

/-- Helper for Theorem 4.30: flattening commutes with affine ray translations. -/
lemma appendEquiv_add_smul
    (x d : MixedRealPoint n p) (a : ℝ) :
    Fin.appendEquiv (α := ℝ) n p (x + a • d) =
      Fin.appendEquiv (α := ℝ) n p x + a • Fin.appendEquiv (α := ℝ) n p d := by
  -- Reuse linearity instead of reproving the blockwise identities again.
  calc
    Fin.appendEquiv (α := ℝ) n p (x + a • d)
        = Fin.appendEquiv (α := ℝ) n p x + Fin.appendEquiv (α := ℝ) n p (a • d) :=
          (isLinearMap_appendEquiv (n := n) (p := p)).map_add x (a • d)
    _ = Fin.appendEquiv (α := ℝ) n p x + a • Fin.appendEquiv (α := ℝ) n p d := by
          rw [(isLinearMap_appendEquiv (n := n) (p := p)).map_smul]

/-- Helper for Theorem 4.30: flattening commutes with convex hull because the flattening map is
linear. -/
lemma appendEquiv_image_convexHull
    (S : Set (MixedRealPoint n p)) :
    Fin.appendEquiv (α := ℝ) n p '' convexHull ℝ S =
      convexHull ℝ (Fin.appendEquiv (α := ℝ) n p '' S) := by
  -- This is the canonical linear-image theorem specialized to the flattening equivalence.
  simpa using (isLinearMap_appendEquiv (n := n) (p := p)).image_convexHull S

/-- Helper for Theorem 4.30: flattening after unflattening is the identity on the ambient
`Fin (n + p)` coordinate space. -/
lemma appendEquiv_symm_apply
    (u : Fin (n + p) → ℝ) :
    Fin.appendEquiv n p ((Fin.appendEquiv n p).symm u) = u := by
  -- Check the two blocks separately so the coercions through `Fin.append` stay syntactic.
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [Fin.appendEquiv]
  · intro j
    simp [Fin.appendEquiv]

/-- Helper for Theorem 4.30: the pointed-cone hull of a set agrees with the Chapter 3 generated
cone of that set. -/
lemma pointedConeHull_eq_cone
    {k : ℕ} (S : Set (Fin k → ℝ)) :
    (PointedCone.hull ℝ S : Set (Fin k → ℝ)) = cone S :=
  rfl

/-- Helper for Theorem 4.30: the integral ray monoid generated by the integral rays `r`. This is
the source object `R_I` from Meyer's decomposition (4.26). -/
def integral_ray_monoid
    {k q : ℕ} (r : Fin q → Fin k → ℤ) : Set (Fin k → ℝ) :=
  {u | ∃ a : Fin q → ℕ, u = ∑ j, (a j : ℝ) • (fun i ↦ (r j i : ℝ))}

/-- Helper for Theorem 4.30: the zero vector belongs to the integral ray monoid. -/
lemma zero_mem_integral_ray_monoid
    {k q : ℕ} (r : Fin q → Fin k → ℤ) :
    (0 : Fin k → ℝ) ∈ integral_ray_monoid r := by
  -- Choose the zero multiplicity vector; the resulting conic combination is the empty ray sum.
  refine ⟨fun _ ↦ 0, ?_⟩
  ext i
  simp

/-- Helper for Theorem 4.30: each generating ray already lies in the integral ray monoid. -/
lemma integral_ray_mem_integral_ray_monoid
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (j : Fin q) :
    (fun i ↦ (r j i : ℝ)) ∈ integral_ray_monoid r := by
  -- Use multiplicity `1` on the chosen ray and `0` on all other rays.
  refine ⟨Pi.single j 1, ?_⟩
  classical
  ext i
  rw [Finset.sum_eq_single j]
  · simp
  · intro c _ hc
    ext i'
    simp [hc]
  · simp

/-- Helper for Theorem 4.30: every integral ray combination is already in the real cone generated
by the same ray family. -/
lemma integral_ray_monoid_subset_cone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) :
    integral_ray_monoid r ⊆ cone (Set.range fun j : Fin q ↦ fun i ↦ (r j i : ℝ)) := by
  intro u hu
  rcases hu with ⟨a, rfl⟩
  -- Reuse the same coefficient family, now viewed over `ℝ`, to obtain cone membership.
  refine (mem_cone_iff).2 ⟨q, (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)), ?_, ?_⟩
  · intro j
    exact ⟨j, rfl⟩
  · refine (isConicCombination_iff).2 ?_
    refine ⟨fun j ↦ (a j : ℝ), ?_, ?_⟩
    · intro j
      positivity
    · rfl

/-- Helper for Theorem 4.30: the integral ray monoid is closed under addition. -/
lemma add_mem_integral_ray_monoid
    {k q : ℕ} {r : Fin q → Fin k → ℤ}
    {u v : Fin k → ℝ}
    (hu : u ∈ integral_ray_monoid r)
    (hv : v ∈ integral_ray_monoid r) :
    u + v ∈ integral_ray_monoid r := by
  rcases hu with ⟨a, rfl⟩
  rcases hv with ⟨b, rfl⟩
  -- Add the multiplicity vectors componentwise and regroup the resulting conic sum.
  refine ⟨fun j ↦ a j + b j, ?_⟩
  -- The new sum is exactly the pointwise regrouping of the two old ray combinations.
  simpa [Nat.cast_add, add_smul, Finset.sum_add_distrib]

/-- Helper for Theorem 4.30: every subset sum of the ray family already lies in the integral ray
monoid. -/
lemma subset_sum_mem_integral_ray_monoid
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (J : Finset (Fin q)) :
    Finset.sum J (fun j ↦ fun i : Fin k ↦ (r j i : ℝ)) ∈ integral_ray_monoid r := by
  induction J using Finset.induction_on with
  | empty =>
      -- The empty subset sum is the zero vector.
      simpa using zero_mem_integral_ray_monoid r
  | @insert j J hj hJ =>
      -- Insert one more ray and use closure of the monoid under addition.
      have hj_mem : (fun i ↦ (r j i : ℝ)) ∈ integral_ray_monoid r :=
        integral_ray_mem_integral_ray_monoid r j
      have hsum_mem :
          Finset.sum J (fun j ↦ fun i : Fin k ↦ (r j i : ℝ)) ∈ integral_ray_monoid r := hJ
      simpa [Finset.sum_insert hj, add_comm, add_left_comm, add_assoc] using
        add_mem_integral_ray_monoid (r := r) hj_mem hsum_mem

/-- Helper for Theorem 4.30: the convex hull of the integral ray monoid is contained in the real
cone generated by the same rays. This is the easy inclusion in Meyer's `conv(R_I) = cone(r)` step.
-/
lemma convexHull_integral_ray_monoid_subset_finitely_generated_cone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) :
    convexHull ℝ (integral_ray_monoid r) ⊆
      finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)) := by
  -- The ambient real cone is convex and already contains every integral ray combination.
  refine convexHull_min (integral_ray_monoid_subset_cone r) ?_
  simpa [finitely_generated_cone] using
    cone_convex (R := ℝ) (Set.range fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ))

/-- Helper for Theorem 4.30: forgetting the last coordinate of the generator family embeds the
smaller integral ray monoid into the larger one. -/
lemma integral_ray_monoid_castSucc_subset
    {k q : ℕ} (r : Fin (q + 1) → Fin k → ℤ) :
    integral_ray_monoid (fun j : Fin q ↦ fun i : Fin k ↦ r j.castSucc i) ⊆
      integral_ray_monoid r := by
  intro u hu
  rcases hu with ⟨a, rfl⟩
  -- Extend the multiplicity vector by `0` on the last ray.
  let a' : Fin (q + 1) → ℕ := Fin.snoc a 0
  refine ⟨a', ?_⟩
  ext i
  rw [Fin.sum_univ_castSucc]
  simp [a', Fin.snoc_castSucc, Fin.snoc_last, add_comm, add_left_comm, add_assoc]

/-- Helper for Theorem 4.30: translating a point in `convexHull ℝ (integral_ray_monoid r)` by one
more integral ray combination keeps it inside the same convex hull. -/
lemma add_mem_convexHull_integral_ray_monoid
    {k q : ℕ} {r : Fin q → Fin k → ℤ}
    {u v : Fin k → ℝ}
    (hu : u ∈ convexHull ℝ (integral_ray_monoid r))
    (hv : v ∈ integral_ray_monoid r) :
    u + v ∈ convexHull ℝ (integral_ray_monoid r) := by
  have htranslate_subset :
      v +ᵥ integral_ray_monoid r ⊆ integral_ray_monoid r := by
    rintro w ⟨z, hz, rfl⟩
    -- The monoid is closed under addition, so every translated generator stays in the monoid.
    simpa [Pi.vadd_def, vadd_eq_add, add_comm] using
      add_mem_integral_ray_monoid (r := r) hv hz
  have htranslate_hull :
      v +ᵥ convexHull ℝ (integral_ray_monoid r) ⊆ convexHull ℝ (integral_ray_monoid r) := by
    -- Push the translation through the convex hull and use the monoid closure on generators.
    rw [← convexHull_vadd]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro w hw
    exact subset_convexHull ℝ _ (htranslate_subset hw)
  have huv :
      u + v ∈ v +ᵥ convexHull ℝ (integral_ray_monoid r) := by
    rw [Set.mem_vadd_set]
    exact ⟨u, hu, by
      ext i
      simp [Pi.vadd_def, vadd_eq_add, add_comm]⟩
  exact htranslate_hull huv

/-- Helper for Theorem 4.30: any coefficient vector in `[0,1]^q` produces a convex combination of
subset sums of the integral rays, so the corresponding point already belongs to
`convexHull ℝ (integral_ray_monoid r)`. -/
lemma fractional_combination_mem_convexHull_integral_ray_monoid
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (μ : Fin q → ℝ)
    (hμ_nonneg : ∀ j : Fin q, 0 ≤ μ j)
    (hμ_le_one : ∀ j : Fin q, μ j ≤ 1) :
    (∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ))) ∈
      convexHull ℝ (integral_ray_monoid r) := by
  induction q with
  | zero =>
      -- With no rays, the only possible fractional combination is the zero vector.
      simpa using
        (subset_convexHull ℝ (integral_ray_monoid r) (zero_mem_integral_ray_monoid r))
  | succ q ih =>
      let rInit : Fin q → Fin k → ℤ := fun j i ↦ r j.castSucc i
      let μInit : Fin q → ℝ := fun j ↦ μ j.castSucc
      have hbase_small :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) ∈
            convexHull ℝ (integral_ray_monoid rInit) := by
        -- First recurse on the initial segment of the generator family.
        exact ih rInit μInit (fun j ↦ hμ_nonneg j.castSucc) (fun j ↦ hμ_le_one j.castSucc)
      have hbase :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) ∈
            convexHull ℝ (integral_ray_monoid r) := by
        -- Embed the smaller monoid into the larger one by keeping the last multiplicity equal to
        -- `0`.
        refine convexHull_min ?_ (convex_convexHull ℝ _) hbase_small
        intro u hu
        exact subset_convexHull ℝ _ (integral_ray_monoid_castSucc_subset (r := r) hu)
      let lastRay : Fin k → ℝ := fun i ↦ (r (Fin.last q) i : ℝ)
      have hbase_plus :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) + lastRay ∈
            convexHull ℝ (integral_ray_monoid r) := by
        -- Add the last generator once; the monoid closure keeps the translation in the hull.
        exact
          add_mem_convexHull_integral_ray_monoid
            (r := r) hbase (integral_ray_mem_integral_ray_monoid r (Fin.last q))
      have hlast :
          μ (Fin.last q) ∈ Set.Icc (0 : ℝ) 1 := ⟨hμ_nonneg _, hμ_le_one _⟩
      have hfinal :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) +
              μ (Fin.last q) • lastRay ∈
            convexHull ℝ (integral_ray_monoid r) := by
        -- Interpolate between the base subset-sum hull point and its translate by the last ray.
        exact (convex_convexHull ℝ (integral_ray_monoid r)).add_smul_mem hbase hbase_plus hlast
      -- Normalize the `Fin (q + 1)` sum into the recursive prefix plus the final ray.
      simpa [rInit, μInit, lastRay, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        add_comm, add_left_comm, add_assoc] using
        hfinal

/-- Helper for Theorem 4.30: the convex hull of the integral ray monoid generated by `r` is
exactly the real cone generated by the same integral rays. This is Meyer's source identity
`conv(R_I) = cone(r)`. -/
lemma convexHull_integral_ray_monoid_eq_finitely_generated_cone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) :
    convexHull ℝ (integral_ray_monoid r) =
      finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)) := by
  apply Set.Subset.antisymm
  · exact convexHull_integral_ray_monoid_subset_finitely_generated_cone r
  · intro u hu
    rcases (mem_finitely_generated_cone_iff).1 hu with ⟨μ, hμ_nonneg, hrepr⟩
    have hintPart :
        (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) ∈
          integral_ray_monoid r := by
      -- The natural floors are already valid multiplicities in the integral ray monoid.
      exact ⟨fun j ↦ ⌊μ j⌋₊, rfl⟩
    have hfracPart :
        (∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ))) ∈
          convexHull ℝ (integral_ray_monoid r) := by
      -- The fractional remainders lie in `[0,1)`, so the previous lemma applies directly.
      exact
        fractional_combination_mem_convexHull_integral_ray_monoid
          r
          (fun j ↦ Int.fract (μ j))
          (fun j ↦ Int.fract_nonneg (μ j))
          (fun j ↦ (Int.fract_lt_one (μ j)).le)
    have hsplit :
        u =
          (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) +
            ∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ)) := by
      -- Split every cone coefficient into its floor and fractional part.
      calc
        u = ∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ)) := hrepr
        _ = ∑ j : Fin q,
              ((((⌊μ j⌋₊ : ℕ) : ℝ) + Int.fract (μ j)) • (fun i : Fin k ↦ (r j i : ℝ))) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [natCast_floor_eq_intCast_floor (hμ_nonneg j), Int.floor_add_fract]
        _ = (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) +
              ∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ)) := by
                simp [add_smul, Finset.sum_add_distrib]
    -- Translate the fractional convex-combination point by the integral floor part.
    rw [hsplit]
    simpa [add_comm] using add_mem_convexHull_integral_ray_monoid hfracPart hintPart

/-- Helper for Theorem 4.30: the empty subset of `ℝ^k` is a rational polyhedron. -/
lemma is_rational_polyhedron_empty
    {k : ℕ} :
    is_rational_polyhedron (∅ : Set (Fin k → ℝ)) := by
  -- The inconsistent single inequality `0 ≤ -1` cuts out the empty set.
  refine ⟨1, 0, fun _ : Fin 1 ↦ (-1 : ℚ), ?_⟩
  ext x
  constructor
  · intro hx
    exact False.elim hx
  · intro hx
    have hx0 : (0 : ℝ) ≤ -1 := by
      simpa [polyhedron_le_set] using hx 0
    linarith

/-- Helper for Theorem 4.30: recession directions are preserved by the flattening equivalence. -/
lemma mem_recessionCone_flatten_iff
    {Q : Set (MixedRealPoint n p)}
    {d : MixedRealPoint n p} :
    Fin.appendEquiv n p d ∈ recessionCone (Fin.appendEquiv n p '' Q) ↔
      d ∈ recessionCone Q := by
  constructor
  · intro hd
    rw [mem_recessionCone_iff] at hd ⊢
    intro x hx a ha
    -- Apply the flattened recession condition at the flattened base point.
    have hImage :
        Fin.appendEquiv n p x + a • Fin.appendEquiv n p d ∈
          Fin.appendEquiv n p '' Q := by
      exact hd ⟨x, hx, rfl⟩ a ha
    rcases hImage with ⟨y, hyQ, hyEq⟩
    -- Injectivity of the flattening equivalence recovers the original translated point.
    have hyFlat : Fin.appendEquiv n p y = Fin.appendEquiv n p (x + a • d) := by
      calc
        Fin.appendEquiv n p y = Fin.appendEquiv n p x + a • Fin.appendEquiv n p d := hyEq
        _ = Fin.appendEquiv n p (x + a • d) := by
              symm
              exact appendEquiv_add_smul (n := n) (p := p) x d a
    have hy : y = x + a • d := (Fin.appendEquiv n p).injective hyFlat
    exact hy ▸ hyQ
  · intro hd
    rw [mem_recessionCone_iff] at hd ⊢
    rintro u ⟨x, hxQ, rfl⟩ a ha
    -- Translate in the mixed space and then flatten the result back.
    refine ⟨x + a • d, hd hxQ a ha, ?_⟩
    exact appendEquiv_add_smul (n := n) (p := p) x d a

/-- Helper for Theorem 4.30: once the flattened mixed polyhedron is known to be nonempty, the
same rational presentation also gives the exact homogeneous recession system. This is the verified
prefix of Meyer's route before the rational cone-generator step. -/
lemma exists_flattened_recession_system_of_nonempty
    {P : Set (MixedRealPoint n p)}
    (hP : is_rational_mixed_polyhedron P)
    (hP_nonempty : Set.Nonempty P) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin (n + p)) ℚ, ∃ b : Fin m → ℚ,
      ((Fin.appendEquiv n p) '' P) =
        polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) ∧
      recessionCone ((Fin.appendEquiv n p) '' P) =
        {r : Fin (n + p) → ℝ | (A.map (Rat.castHom ℝ)) *ᵥ r ≤ 0} := by
  let Pflat : Set (Fin (n + p) → ℝ) := (Fin.appendEquiv n p) '' P
  have hPflat : is_rational_polyhedron Pflat := by
    simpa [Pflat] using hP
  rcases hPflat with ⟨m, A, b, hPflat_eq⟩
  have hPflat_nonempty : Set.Nonempty Pflat := by
    rcases hP_nonempty with ⟨xy, hxy⟩
    exact ⟨Fin.appendEquiv n p xy, ⟨xy, hxy, rfl⟩⟩
  have hrec_hom :
      recessionCone Pflat =
        {r : Fin (n + p) → ℝ | (A.map (Rat.castHom ℝ)) *ᵥ r ≤ 0} := by
    -- Route correction: pin down the recession cone first, before any truncation or vertex work.
    calc
      recessionCone Pflat
          = recessionCone
              (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) := by
                rw [hPflat_eq]
      _ = {r : Fin (n + p) → ℝ | (A.map (Rat.castHom ℝ)) *ᵥ r ≤ 0} := by
            exact
              polyhedron_recessionCone_eq_homogeneous_solution_set
                (A.map (Rat.castHom ℝ))
                (fun i ↦ (b i : ℝ))
                (by simpa [hPflat_eq] using hPflat_nonempty)
  exact ⟨m, A, b, hPflat_eq, by simpa [Pflat] using hrec_hom⟩

/-- Helper for Theorem 4.30: nonemptiness of the mixed-integer set gives the same flattened
homogeneous recession system, now stated under the source hypothesis that actually appears in
Meyer. -/
lemma exists_flattened_recession_system
    {P : Set (MixedRealPoint n p)}
    (hP : is_rational_mixed_polyhedron P)
    (hS_nonempty : Set.Nonempty (mixed_integer_points P)) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin (n + p)) ℚ, ∃ b : Fin m → ℚ,
      ((Fin.appendEquiv n p) '' P) =
        polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) ∧
      recessionCone ((Fin.appendEquiv n p) '' P) =
        {r : Fin (n + p) → ℝ | (A.map (Rat.castHom ℝ)) *ᵥ r ≤ 0} := by
  -- Forget the integrality condition to recover the feasible base point needed by Proposition 3.15.
  exact
    exists_flattened_recession_system_of_nonempty
      (P := P) hP (nonempty_of_mixed_integer_points_nonempty (P := P) hS_nonempty)

/-- Helper for Theorem 4.30: the common denominator of a rational vector is always nonzero. -/
lemma rational_vector_common_denominator_ne_zero
    {k : ℕ} (v : Fin k → ℚ) :
    rational_vector_common_denominator v ≠ 0 := by
  -- Every coordinate denominator is positive, so their finite least common multiple is nonzero.
  have hden :
      ∀ i ∈ (Finset.univ : Finset (Fin k)), (v i).den ≠ 0 := by
    intro i hi
    exact Nat.ne_of_gt (Rat.den_pos (v i))
  simpa [rational_vector_common_denominator] using
    (Finset.lcm_ne_zero_iff.2 hden)

/-- Helper for Theorem 4.30: clearing a rational vector's common denominator gives the same vector
after scalar extension to `ℝ`, up to the obvious positive scalar. -/
lemma common_denominator_scaled_vector_eq_smul_real
    {k : ℕ} (v : Fin k → ℚ) :
    (fun i ↦ (common_denominator_scaled_vector v i : ℝ)) =
      (rational_vector_common_denominator v : ℝ) • (fun i ↦ (v i : ℝ)) := by
  ext i
  change ((common_denominator_scaled_vector v i : ℤ) : ℝ) =
      (rational_vector_common_denominator v : ℝ) * (v i : ℝ)
  -- First use the rational common-denominator identity, then cast it into `ℝ`.
  have hi :
      ((common_denominator_scaled_vector v i : ℤ) : ℚ) =
        (rational_vector_common_denominator v : ℚ) * v i := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      congrFun (common_denominator_scaled_vector_eq_smul v) i
  exact_mod_cast hi

/-- Helper for Theorem 4.30: clearing denominators ray-by-ray preserves the generated real cone. -/
lemma commonDenominatorScaledRays_eq_finitely_generated_cone
    {k q : ℕ} (r : Fin q → Fin k → ℚ) :
    finitely_generated_cone
        (fun j : Fin q ↦ fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) =
      finitely_generated_cone
        (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, hrepr⟩
    have hD_nonneg :
        ∀ j : Fin q, 0 ≤ (rational_vector_common_denominator (r j) : ℝ) := by
      intro j
      exact_mod_cast Nat.zero_le (rational_vector_common_denominator (r j))
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j * (rational_vector_common_denominator (r j) : ℝ), ?_, ?_⟩
    · -- Multiplying by a nonnegative common denominator preserves cone coefficients.
      intro j
      exact mul_nonneg (hμ_nonneg j) (hD_nonneg j)
    · -- Rewrite every cleared ray as a positive scalar multiple of its original rational ray.
      calc
        x = ∑ j : Fin q, μ j • (fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) :=
              hrepr
        _ = ∑ j : Fin q,
              (μ j * (rational_vector_common_denominator (r j) : ℝ)) •
                (fun i : Fin k ↦ (r j i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [common_denominator_scaled_vector_eq_smul_real (v := r j), smul_smul]
  · intro x hx
    rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, hrepr⟩
    have hD_nonneg :
        ∀ j : Fin q, 0 ≤ (rational_vector_common_denominator (r j) : ℝ) := by
      intro j
      exact_mod_cast Nat.zero_le (rational_vector_common_denominator (r j))
    have hD_ne_zero :
        ∀ j : Fin q, (rational_vector_common_denominator (r j) : ℝ) ≠ 0 := by
      intro j
      exact_mod_cast rational_vector_common_denominator_ne_zero (v := r j)
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j / (rational_vector_common_denominator (r j) : ℝ), ?_, ?_⟩
    · -- Dividing by a positive common denominator keeps coefficients nonnegative.
      intro j
      exact div_nonneg (hμ_nonneg j) (hD_nonneg j)
    · -- Undo the denominator-clearing by dividing each coefficient by the same positive scalar.
      calc
        x = ∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ)) := hrepr
        _ = ∑ j : Fin q,
              (μ j / (rational_vector_common_denominator (r j) : ℝ)) •
                (fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [common_denominator_scaled_vector_eq_smul_real (v := r j), smul_smul,
                div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (hD_ne_zero j), mul_one]

/-- Helper for Theorem 4.30: a nonempty flattened rational mixed polyhedron admits finitely many
integral generators for its recession cone. -/
lemma exists_flattened_integral_recession_generators
    {P : Set (MixedRealPoint n p)}
    (hP : is_rational_mixed_polyhedron P)
    (hP_nonempty : Set.Nonempty P) :
    ∃ q : ℕ,
      ∃ rays : Fin q → Fin (n + p) → ℤ,
        recessionCone ((Fin.appendEquiv n p) '' P) =
          finitely_generated_cone (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (rays j i : ℝ)) := by
  rcases exists_flattened_recession_system_of_nonempty (P := P) hP hP_nonempty with
    ⟨m, A, b, -, hrec_hom⟩
  rcases exists_rational_matrix_cone_of_rational_matrix_polyhedral_cone A with ⟨q, R, hR⟩
  let raysQ : Fin q → Fin (n + p) → ℚ := fun j i ↦ R i j
  let raysInt : Fin q → Fin (n + p) → ℤ := fun j ↦ common_denominator_scaled_vector (raysQ j)
  refine ⟨q, raysInt, ?_⟩
  -- Normalize the homogeneous rational system to a rational matrix cone, then clear
  -- denominators on each rational generator once and for all.
  calc
    recessionCone ((Fin.appendEquiv n p) '' P)
        = matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) := by
            simpa [matrix_polyhedral_cone] using hrec_hom
    _ = (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin (n + p) → ℝ)) := hR
    _ = finitely_generated_cone (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (raysQ j i : ℝ)) := by
          simpa [raysQ] using
            (finitely_generated_cone_eq_matrix_cone
              (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (raysQ j i : ℝ))).symm
    _ = finitely_generated_cone (fun j : Fin q ↦ fun i : Fin (n + p) ↦ (raysInt j i : ℝ)) := by
          simpa [raysInt, raysQ] using
            (commonDenominatorScaledRays_eq_finitely_generated_cone
              (r := raysQ)).symm

/-- Helper for Theorem 4.30: every rational polyhedron is, in particular, a polyhedron. -/
lemma is_polyhedron_of_is_rational_polyhedron
    {k : ℕ} {Q : Set (Fin k → ℝ)}
    (hQ : is_rational_polyhedron Q) :
    is_polyhedron Q := by
  rcases hQ with ⟨m, A, b, rfl⟩
  -- Forget the coefficient field restriction and keep the same inequality system over `ℝ`.
  exact ⟨m, A.map (Rat.castHom ℝ), fun i ↦ (b i : ℝ), rfl⟩

/-- Helper for Theorem 4.30: polyhedra presented by finitely many linear inequalities are
closed. -/
lemma isClosed_polyhedron_le_set_local
    {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (b : Fin m → ℝ) :
    IsClosed (polyhedron_le_set A b) := by
  rw [show polyhedron_le_set A b = ⋂ i : Fin m, {x : Fin k → ℝ | (A *ᵥ x) i ≤ b i} by
    ext x
    constructor
    · intro hx
      simpa [polyhedron_le_set] using hx
    · intro hx
      simpa [polyhedron_le_set] using hx]
  refine isClosed_iInter ?_
  intro i
  have hcont : Continuous fun x : Fin k → ℝ ↦ (A *ᵥ x) i := by
    exact (continuous_apply i).comp A.mulVecLin.continuous_of_finiteDimensional
  exact isClosed_le hcont continuous_const

/-- Helper for Theorem 4.30: polyhedra presented by finitely many linear inequalities are
convex. -/
lemma convex_polyhedron_le_set_local
    {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  rw [show polyhedron_le_set A b = ⋂ i : Fin m, {x : Fin k → ℝ | (A *ᵥ x) i ≤ b i} by
    ext x
    constructor
    · intro hx
      simpa [polyhedron_le_set] using hx
    · intro hx
      simpa [polyhedron_le_set] using hx]
  refine convex_iInter ?_
  intro i
  let L : (Fin k → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ (A *ᵥ x) i
      map_add' := by
        intro x y
        exact congrFun (Matrix.mulVec_add A x y) i
      map_smul' := by
        intro a x
        exact congrFun (Matrix.mulVec_smul A a x) i }
  have hconv : Convex ℝ (Set.Iic (b i)) := convex_Iic _
  simpa [L] using hconv.linear_preimage L

/-- Helper for Theorem 4.30: the recession cone of a nonempty polyhedron is closed. -/
lemma isClosed_recessionCone_polyhedron_local
    {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    IsClosed (recessionCone (polyhedron_le_set A b)) := by
  rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b h_nonempty]
  simpa using isClosed_polyhedron_le_set_local A (0 : Fin m → ℝ)

/-- Helper for Theorem 4.30: adding a nonnegative multiple of one cone element to another stays in
the same finitely generated cone. -/
lemma finitely_generated_cone_add_smul_mem_local
    {k q : ℕ} (rays : Fin q → Fin k → ℝ)
    {y r : Fin k → ℝ}
    (hy : y ∈ finitely_generated_cone rays)
    (hr : r ∈ finitely_generated_cone rays)
    {a : ℝ} (ha : 0 ≤ a) :
    y + a • r ∈ finitely_generated_cone rays := by
  rcases (mem_finitely_generated_cone_iff.mp hy) with ⟨μ, hμ_nonneg, rfl⟩
  rcases (mem_finitely_generated_cone_iff.mp hr) with ⟨ν, hν_nonneg, rfl⟩
  refine mem_finitely_generated_cone_iff.mpr ⟨fun i ↦ μ i + a * ν i, ?_, ?_⟩
  · intro i
    exact add_nonneg (hμ_nonneg i) (mul_nonneg ha (hν_nonneg i))
  · calc
      (∑ i, μ i • rays i) + a • ∑ i, ν i • rays i
          = (∑ i, μ i • rays i) + ∑ i, (a * ν i) • rays i := by
              congr 1
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [smul_smul]
      _ = ∑ i, (μ i + a * ν i) • rays i := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [add_smul]

/-- Helper for Theorem 4.30: if a nonempty polyhedron is written as a finite convex hull plus a
finitely generated cone, then its recession cone is exactly that cone. -/
lemma recessionCone_eq_finitely_generated_cone_of_polyhedron_repr
    {m k p q : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ)
    (b : Fin m → ℝ)
    (vertices : Fin p → Fin k → ℝ)
    (rays : Fin q → Fin k → ℝ)
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b))
    (h_repr :
      polyhedron_le_set A b =
        convexHull ℝ (Set.range vertices) + finitely_generated_cone rays) :
    recessionCone (polyhedron_le_set A b) = closure (finitely_generated_cone rays) := by
  let K : Set (Fin k → ℝ) := convexHull ℝ (Set.range vertices)
  let C : Set (Fin k → ℝ) := finitely_generated_cone rays
  have hK_bounded : Bornology.IsBounded K := by
    dsimp [K]
    exact (isBounded_convexHull).2 (Set.finite_range vertices).isBounded
  have hx0K : ∃ x0 : Fin k → ℝ, x0 ∈ K := by
    rcases h_nonempty with ⟨x, hx⟩
    rw [h_repr] at hx
    rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, hsum⟩
    exact ⟨y, hy⟩
  rcases hx0K with ⟨x0, hx0K⟩
  have hzeroC : (0 : Fin k → ℝ) ∈ C := by
    dsimp [C, finitely_generated_cone]
    exact cone_zero_mem
  have hx0P : x0 ∈ polyhedron_le_set A b := by
    rw [h_repr]
    refine Set.mem_add.mpr ⟨x0, hx0K, 0, hzeroC, ?_⟩
    simp
  ext r
  constructor
  · intro hr
    rw [mem_recessionCone_iff] at hr
    have hdecomp :
        ∀ n : ℕ,
          ∃ y z,
            y ∈ K ∧ z ∈ C ∧ y + z = x0 + (((n : ℝ) + 1) • r) := by
      intro n
      have hxnr : x0 + (((n : ℝ) + 1) • r) ∈ polyhedron_le_set A b := by
        exact hr hx0P (((n : ℝ) + 1)) (by positivity)
      rw [h_repr] at hxnr
      rcases Set.mem_add.mp hxnr with ⟨y, hy, z, hz, hsum⟩
      exact ⟨y, z, hy, hz, hsum⟩
    choose y z hyK hzC hsum using hdecomp
    let δ : ℕ → ℝ := fun n ↦ (((n : ℝ) + 1)⁻¹)
    let u : ℕ → Fin k → ℝ := fun n ↦ δ n • z n
    have hδ_nonneg : ∀ n : ℕ, 0 ≤ δ n := by
      intro n
      dsimp [δ]
      positivity
    have hu_mem : ∀ n : ℕ, u n ∈ C := by
      intro n
      exact IsCone.smul_mem' (C := C) (hzC n) (hδ_nonneg n)
    have hu_eq :
        ∀ n : ℕ, u n = r + δ n • (x0 - y n) := by
      intro n
      have hscale_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hz_eq : z n = x0 + (((n : ℝ) + 1) • r) - y n := by
        exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hsum n)
      calc
        u n = δ n • (x0 + (((n : ℝ) + 1) • r) - y n) := by
          dsimp [u]
          rw [hz_eq]
        _ = δ n • (x0 + (((n : ℝ) + 1) • r)) - δ n • y n := by
              rw [smul_sub]
        _ = (δ n • x0 + δ n • (((n : ℝ) + 1) • r)) - δ n • y n := by
              rw [smul_add]
        _ = (δ n • x0 + r) - δ n • y n := by
              congr 1
              rw [smul_smul, inv_mul_cancel₀ hscale_ne, one_smul]
        _ = r + (δ n • x0 - δ n • y n) := by
              simp [sub_eq_add_neg, add_assoc, add_comm]
        _ = r + δ n • (x0 - y n) := by
              rw [smul_sub]
    have hdiff_bounded : Bornology.IsBounded (Set.range fun n : ℕ ↦ x0 - y n) := by
      refine
        (isBounded_sub
          (show Bornology.IsBounded ({x0} : Set (Fin k → ℝ)) from Bornology.isBounded_singleton)
          hK_bounded).subset ?_
      intro v hv
      rcases hv with ⟨n, rfl⟩
      exact Set.sub_mem_sub (by simp) (hyK n)
    have hnorm_bounded :
        Filter.IsBoundedUnder (· ≤ ·) (Filter.atTop : Filter ℕ) (norm ∘ fun n : ℕ ↦ x0 - y n) := by
      obtain ⟨R, hR⟩ := hdiff_bounded.subset_closedBall (0 : Fin k → ℝ)
      refine Filter.isBoundedUnder_of ?_
      refine ⟨R, ?_⟩
      intro n
      have hmem : x0 - y n ∈ Set.range (fun t : ℕ ↦ x0 - y t) := Set.mem_range_self n
      have hball : x0 - y n ∈ Metric.closedBall (0 : Fin k → ℝ) R := hR hmem
      simpa [Metric.mem_closedBall, dist_eq_norm] using hball
    have hδ_tendsto : Filter.Tendsto δ (Filter.atTop : Filter ℕ) (nhds 0) := by
      simpa [δ, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) (Filter.atTop : Filter ℕ) (nhds 0))
    have herr_tendsto :
        Filter.Tendsto (fun n : ℕ ↦ δ n • (x0 - y n)) (Filter.atTop : Filter ℕ) (nhds 0) :=
      NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hδ_tendsto hnorm_bounded
    have hu_tendsto : Filter.Tendsto u (Filter.atTop : Filter ℕ) (nhds r) := by
      have htarget :
          Filter.Tendsto (fun n : ℕ ↦ r + δ n • (x0 - y n)) (Filter.atTop : Filter ℕ) (nhds r) := by
        simpa using (tendsto_const_nhds.add herr_tendsto)
      refine Filter.Tendsto.congr' ?_ htarget
      exact Filter.Eventually.of_forall fun n ↦ (hu_eq n).symm
    exact
      isClosed_closure.mem_of_tendsto
        hu_tendsto
        (Filter.Eventually.of_forall fun n ↦ subset_closure (hu_mem n))
  · intro hr
    have hcone_subset : C ⊆ recessionCone (polyhedron_le_set A b) := by
      intro r hr
      rw [mem_recessionCone_iff]
      intro x hx a ha
      rw [h_repr] at hx ⊢
      rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, hsum⟩
      have hz' : z + a • r ∈ C := by
        exact finitely_generated_cone_add_smul_mem_local rays hz hr ha
      refine Set.mem_add.mpr ⟨y, hy, z + a • r, hz', ?_⟩
      simpa [C, add_assoc] using congrArg (fun t ↦ t + a • r) hsum
    exact
      (closure_minimal hcone_subset
        (isClosed_recessionCone_polyhedron_local A b h_nonempty)) hr

/-- Helper for Theorem 4.30: a finite polytope presentation can be reindexed onto a `Fin` family
of vertices. This is the canonical bridge from `Q.IsPolytope` to the `Fin`-indexed Chapter 3 API.
-/
lemma exists_convexHull_range_eq_of_isPolytope
    {k : ℕ} {Q : Set (Fin k → ℝ)}
    (hQ_polytope : Q.IsPolytope ℝ) :
    ∃ p : ℕ, ∃ vertices : Fin p → Fin k → ℝ, Q = convexHull ℝ (Set.range vertices) := by
  rcases hQ_polytope with ⟨V, hV_finite, hQ_eq⟩
  let s : Finset (Fin k → ℝ) := hV_finite.toFinset
  let vertices : Fin s.card → Fin k → ℝ := fun i ↦ ((Finset.equivFin s).symm i).1
  have hV_range : Set.range vertices = V := by
    -- Reindex the finite vertex set onto a canonical `Fin` family.
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      have hi_mem : (((Finset.equivFin s).symm i).1) ∈ (s : Set (Fin k → ℝ)) :=
        ((Finset.equivFin s).symm i).2
      simpa [vertices, s] using hi_mem
    · intro hx
      have hx' : x ∈ (s : Set (Fin k → ℝ)) := by
        simpa [s] using hx
      refine ⟨(Finset.equivFin s) ⟨x, hx'⟩, ?_⟩
      simp [vertices]
  exact ⟨s.card, vertices, by rw [hQ_eq, ← hV_range]⟩

/-- Helper for Theorem 4.30: a finite rational vertex family can always be reindexed onto a
`Fin`-indexed rational polytope presentation. -/
lemma convexHull_range_isRationalPolytope_of_fintype
    {k : ℕ}
    {ι : Type*}
    [Fintype ι]
    (vertex : ι → Fin k → ℚ) :
    (convexHull ℝ (Set.range fun j : ι ↦ fun i : Fin k ↦ (vertex j i : ℝ))).IsRationalPolytope := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun j i ↦ vertex (e j) i, ?_⟩
  ext x
  constructor
  · intro hx
    have hrange :
        Set.range (fun j : Fin (Fintype.card ι) ↦ fun i : Fin k ↦ ((vertex (e j) i : ℚ) : ℝ)) =
          Set.range (fun j : ι ↦ fun i : Fin k ↦ (vertex j i : ℝ)) := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, by simp [e]⟩
    simpa [hrange] using hx
  · intro hx
    have hrange :
        Set.range (fun j : Fin (Fintype.card ι) ↦ fun i : Fin k ↦ ((vertex (e j) i : ℚ) : ℝ)) =
          Set.range (fun j : ι ↦ fun i : Fin k ↦ (vertex j i : ℝ)) := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, by simp [e]⟩
    simpa [hrange] using hx

/-- Helper for Theorem 4.30: the convex hull of a finite union of rational polytopes is again a
rational polytope. -/
lemma convexHull_iUnion_isRationalPolytope
    {d k : ℕ}
    (Q : Fin k → Set (Fin d → ℝ))
    (hQ : ∀ i, (Q i).IsRationalPolytope) :
    (convexHull ℝ (⋃ i : Fin k, Q i)).IsRationalPolytope := by
  classical
  choose m vertex hvertex using hQ
  let allVertices : Sigma (fun i : Fin k ↦ Fin (m i)) → Fin d → ℚ :=
    fun a ↦ vertex a.1 a.2
  have hvertex_subset :
      Set.range (fun a : Sigma (fun i : Fin k ↦ Fin (m i)) ↦
          fun j : Fin d ↦ (allVertices a j : ℝ)) ⊆
        ⋃ i : Fin k, Q i := by
    rintro x ⟨a, rfl⟩
    have hx :
        (fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) ∈
          convexHull ℝ (Set.range fun t : Fin (m a.1) ↦ fun j : Fin d ↦ (vertex a.1 t j : ℝ)) :=
      subset_convexHull ℝ _ ⟨a.2, rfl⟩
    rw [← hvertex a.1] at hx
    exact Set.mem_iUnion.2 ⟨a.1, hx⟩
  have hiUnion_subset :
      (⋃ i : Fin k, Q i) ⊆
        convexHull ℝ
          (Set.range fun a : Sigma (fun i : Fin k ↦ Fin (m i)) ↦
            fun j : Fin d ↦ (allVertices a j : ℝ)) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
    rw [hvertex i] at hx
    refine (convexHull_mono ?_) hx
    rintro y ⟨j, rfl⟩
    exact ⟨⟨i, j⟩, rfl⟩
  have hEq :
      convexHull ℝ (⋃ i : Fin k, Q i) =
        convexHull ℝ
          (Set.range fun a : Sigma (fun i : Fin k ↦ Fin (m i)) ↦
            fun j : Fin d ↦ (allVertices a j : ℝ)) := by
    apply Set.Subset.antisymm
    · exact convexHull_min hiUnion_subset (convex_convexHull ℝ _)
    · refine convexHull_min ?_ (convex_convexHull ℝ _)
      intro x hx
      exact subset_convexHull ℝ _ (hvertex_subset hx)
  rw [hEq]
  exact convexHull_range_isRationalPolytope_of_fintype allVertices

/-- Helper for Theorem 4.30: flattening sends the mixed integer cone from Corollary 4.31 to the
ordinary integral cone generated by the flattened directions. -/
lemma appendEquiv_image_mixed_integer_intcone
    {q : ℕ}
    (r : Fin q → (Fin n → ℤ) × (Fin p → ℤ)) :
    Fin.appendEquiv n p '' mixed_integer_intcone r =
      integral_intcone (fun j : Fin q ↦ Fin.append (r j).1 (r j).2) := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨v, hv, rfl⟩
    rw [appendEquiv_symm_apply (n := n) (p := p) v]
    exact hv
  · intro hu
    refine ⟨(Fin.appendEquiv n p).symm u, ?_, ?_⟩
    refine ⟨u, hu, ?_⟩
    ext i <;> simp [Fin.appendEquiv]
    simpa using appendEquiv_symm_apply (n := n) (p := p) u

/-- Helper for Theorem 4.30: the convex hull of the integral cone generated by `r` is the real
cone generated by the same rays. -/
lemma convexHull_integral_intcone_eq_finitely_generated_cone
    {k q : ℕ}
    (r : Fin q → Fin k → ℤ) :
    convexHull ℝ (integral_intcone r) =
      finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)) := by
  simpa [integral_intcone, integral_ray_monoid] using
    convexHull_integral_ray_monoid_eq_finitely_generated_cone r

/-- Helper for Theorem 4.30: flattening distributes over the finite-union-plus-integer-cone
decomposition from Corollary 4.31. -/
lemma appendEquiv_image_iUnion_add_mixed_integer_intcone
    {k q : ℕ}
    (P' : Fin k → Set (MixedRealPoint n p))
    (r : Fin q → (Fin n → ℤ) × (Fin p → ℤ)) :
    Fin.appendEquiv n p '' ((⋃ i : Fin k, P' i) + mixed_integer_intcone r) =
      (⋃ i : Fin k, Fin.appendEquiv n p '' P' i) +
        integral_intcone (fun j : Fin q ↦ Fin.append (r j).1 (r j).2) := by
  ext u
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    rcases hxy with ⟨a, ha, b, hb, rfl⟩
    rcases Set.mem_iUnion.1 ha with ⟨i, hai⟩
    have hb' : Fin.appendEquiv n p b ∈ integral_intcone (fun j : Fin q ↦ Fin.append (r j).1 (r j).2) := by
      rw [← appendEquiv_image_mixed_integer_intcone (n := n) (p := p) (r := r)]
      exact ⟨b, hb, rfl⟩
    refine Set.mem_add.2 ⟨Fin.appendEquiv n p a, ?_, Fin.appendEquiv n p b, ?_, ?_⟩
    · exact Set.mem_iUnion.2 ⟨i, ⟨a, hai, rfl⟩⟩
    · exact hb'
    · simpa using ((isLinearMap_appendEquiv (n := n) (p := p)).map_add a b).symm
  · rintro ⟨u₁, hu₁, u₂, hu₂, hu_eq⟩
    rcases Set.mem_iUnion.1 hu₁ with ⟨i, hu₁⟩
    rcases hu₁ with ⟨a, ha, rfl⟩
    have hu₂' : (Fin.appendEquiv n p).symm u₂ ∈ mixed_integer_intcone r := by
      exact ⟨u₂, hu₂, rfl⟩
    refine ⟨a + (Fin.appendEquiv n p).symm u₂, Set.mem_add.2 ⟨a, Set.mem_iUnion.2 ⟨i, ha⟩,
      (Fin.appendEquiv n p).symm u₂, hu₂', rfl⟩, ?_⟩
    calc
      Fin.appendEquiv n p (a + (Fin.appendEquiv n p).symm u₂)
          = Fin.appendEquiv n p a + Fin.appendEquiv n p ((Fin.appendEquiv n p).symm u₂) := by
              simpa using
                (isLinearMap_appendEquiv (n := n) (p := p)).map_add a
                  ((Fin.appendEquiv n p).symm u₂)
      _ = Fin.appendEquiv n p a + u₂ := by
            congr 1
            simpa using appendEquiv_symm_apply (n := n) (p := p) u₂
      _ = u := hu_eq

/-- Helper for Theorem 4.30: the flattened mixed-integer set sits inside the flattened ambient
polyhedron. -/
lemma flattened_mixed_integer_points_subset
    {P : Set (MixedRealPoint n p)} :
    (Fin.appendEquiv n p '' mixed_integer_points P) ⊆ (Fin.appendEquiv n p '' P) := by
  intro u hu
  -- Forget the first-block integrality condition in the flattened membership test.
  exact (mem_flattened_mixed_integer_points_iff (P := P) (u := u)).1 hu |>.1

/-- Helper for Theorem 4.30: with zero integer coordinates, taking mixed-integer points does not
change the set. -/
lemma mixed_integer_points_eq_self_zero_integer_block
    {k : ℕ} (Q : Set (MixedRealPoint 0 k)) :
    mixed_integer_points Q = Q := by
  ext xy
  constructor
  · intro hxy
    -- Forgetting the vacuous integrality condition recovers the original point of `Q`.
    exact (mem_mixed_integer_points_iff).1 hxy |>.1
  · intro hxy
    -- Route correction: the ambient flattened set is a mixed set with no integer coordinates, so
    -- the lattice side condition is automatic.
    refine (mem_mixed_integer_points_iff).2 ⟨hxy, ?_⟩
    rw [mem_mixed_integer_lattice_iff, mem_integerVectors_iff]
    refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
    funext i
    exact Fin.elim0 i

/-- Helper for Theorem 4.30: flattening a point with zero integer block and restricting to the
nonempty coordinates recovers its second block. -/
lemma appendEquiv_zero_left_drop
    {k : ℕ} (xy : MixedRealPoint 0 k) :
    (fun i : Fin k ↦ Fin.appendEquiv 0 k xy (Fin.cast (by simp) i)) = xy.2 := by
  ext i
  simpa [Fin.cast_natAdd, Fin.appendEquiv] using Fin.append_right xy.1 xy.2 i

/-- Helper for Theorem 4.30: the integral cone is closed under addition. -/
lemma add_mem_integral_intcone
    {k q : ℕ} {r : Fin q → Fin k → ℤ}
    {u v : Fin k → ℝ}
    (hu : u ∈ integral_intcone r)
    (hv : v ∈ integral_intcone r) :
    u + v ∈ integral_intcone r := by
  -- This is exactly the additive closure already established for the matching ray monoid.
  simpa [integral_intcone, integral_ray_monoid] using
    add_mem_integral_ray_monoid (r := r) hu hv

/-- Helper for Theorem 4.30: every natural multiple of a listed integral generator lies in the
integral cone generated by the whole family. -/
lemma nat_smul_generator_mem_integral_intcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (j : Fin q) (m : ℕ) :
    (m : ℝ) • (fun i : Fin k ↦ (r j i : ℝ)) ∈ integral_intcone r := by
  refine (mem_integral_intcone_iff).2 ?_
  refine ⟨fun t ↦ if t = j then m else 0, ?_⟩
  ext i
  rw [Finset.sum_eq_single j]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

/-- Helper for Theorem 4.30: adding a natural multiple of an integral vector preserves
`integerVectors`. -/
lemma integerVectors_add_nat_smul_of_integral
    {k : ℕ} {x : Fin k → ℝ}
    (hx : x ∈ integerVectors k)
    (z : Fin k → ℤ)
    (m : ℕ) :
    (fun i : Fin k ↦ x i + (m : ℝ) * (z i : ℝ)) ∈ integerVectors k := by
  rcases (mem_integerVectors_iff (x := x)).1 hx with ⟨a, ha⟩
  refine (mem_integerVectors_iff (x := fun i : Fin k ↦ x i + (m : ℝ) * (z i : ℝ))).2 ?_
  refine ⟨fun i ↦ a i + (m : ℤ) * z i, ?_⟩
  ext i
  simp [ha, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- Helper for Theorem 4.30: for a polyhedron, natural-translate closure of one feasible base
point already forces a recession direction. -/
lemma mem_recessionCone_of_natTranslateMem
    {k m : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ)
    (b : Fin m → ℝ)
    {x₀ r : Fin k → ℝ}
    (hx₀ : x₀ ∈ polyhedron_le_set A b)
    (htranslate : ∀ t : ℕ, x₀ + (t : ℝ) • r ∈ polyhedron_le_set A b) :
    r ∈ recessionCone (polyhedron_le_set A b) := by
  have h_nonempty : Set.Nonempty (polyhedron_le_set A b) := ⟨x₀, hx₀⟩
  rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b h_nonempty]
  intro i
  by_contra hri
  have hri_pos : 0 < (A *ᵥ r) i := lt_of_not_ge hri
  obtain ⟨t, ht⟩ := exists_nat_gt ((b i - (A *ᵥ x₀) i + 1) / (A *ᵥ r) i)
  have hxt : x₀ + (t : ℝ) • r ∈ polyhedron_le_set A b := htranslate t
  have hrow : (A *ᵥ x₀) i + (t : ℝ) * (A *ᵥ r) i ≤ b i := by
    simpa [polyhedron_le_set, Matrix.mulVec_add, Matrix.mulVec_smul] using hxt i
  have hmul : b i - (A *ᵥ x₀) i + 1 < (t : ℝ) * (A *ᵥ r) i := by
    have ht' : ((b i - (A *ᵥ x₀) i + 1) / (A *ᵥ r) i) < (t : ℝ) := by
      exact_mod_cast ht
    exact (div_lt_iff₀ hri_pos).1 ht'
  linarith

/-- Helper for Theorem 4.30: if every listed generator is a recession direction, then the whole
finitely generated cone is contained in the recession cone. -/
lemma finitelyGeneratedCone_subset_recessionCone_of_generator_mem
    {k q : ℕ}
    {Q : Set (Fin k → ℝ)}
    {rays : Fin q → Fin k → ℝ}
    (hgen : ∀ j : Fin q, rays j ∈ recessionCone Q) :
    finitely_generated_cone rays ⊆ recessionCone Q := by
  intro x hx
  rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, rfl⟩
  -- The recession directions form a pointed cone, so nonnegative linear combinations stay inside.
  have hterm :
      ∀ j : Fin q, μ j • rays j ∈ recessionCone Q := by
    intro j
    exact smul_mem_recessionCone (hgen j) (hμ_nonneg j)
  have hsum :
      ∑ j : Fin q, μ j • rays j ∈
        ((recessionPointedCone ℝ Q : PointedCone ℝ (Fin k → ℝ)) : Set (Fin k → ℝ)) := by
    exact Submodule.sum_mem (recessionPointedCone ℝ Q) (fun j _ ↦ hterm j)
  simpa using hsum

/-- Helper for Theorem 4.30: specializing Corollary 4.31 to a zero integer block decomposes the
flattened ambient set into a finite union of rational polytopes plus one integral cone. -/
lemma exists_flattened_ambient_integral_decomposition
    {P : Set (MixedRealPoint n p)}
    (hP : is_rational_mixed_polyhedron P) :
    ∃ k q : ℕ,
      ∃ Q : Fin k → Set (Fin (n + p) → ℝ),
        ∃ r : Fin q → Fin (n + p) → ℤ,
          (∀ i : Fin k, (Q i).IsRationalPolytope) ∧
            (Fin.appendEquiv n p '' P) = (⋃ i : Fin k, Q i) + integral_intcone r := by
  rcases (show is_rational_polyhedron ((Fin.appendEquiv n p) '' P) from hP) with
    ⟨m, A, b, hPflat_eq⟩
  let Pzero : Set (MixedRealPoint 0 (n + p)) :=
    rational_mixed_polyhedron (0 : Matrix (Fin m) (Fin 0) ℚ) A b
  have hPzero : is_rational_mixed_polyhedron Pzero := by
    exact (is_rational_mixed_polyhedron_iff).2 ⟨m, 0, A, b, rfl⟩
  rcases mixed_integer_points_eq_iUnion_rational_polytopes_add_intcone
      (P := Pzero) hPzero with ⟨k, q, Q, r, hQ, hPzero_repr_mixed⟩
  have hPzero_repr :
      Pzero = (⋃ i : Fin k, Q i) + mixed_integer_intcone r := by
    simpa [mixed_integer_points_eq_self_zero_integer_block (Q := Pzero)] using hPzero_repr_mixed
  let dropZero : (Fin (0 + (n + p)) → ℝ) → Fin (n + p) → ℝ :=
    fun u i ↦ u (Fin.cast (by simp) i)
  have hdropZeroLinear : IsLinearMap ℝ dropZero := by
    refine ⟨?_, ?_⟩
    · intro u v
      ext i
      simp [dropZero]
    · intro a u
      ext i
      simp [dropZero]
  let Qflat : Fin k → Set (Fin (n + p) → ℝ) :=
    fun i ↦ dropZero '' (Fin.appendEquiv 0 (n + p) '' Q i)
  have hQflat : ∀ i : Fin k, (Qflat i).IsRationalPolytope := by
    intro i
    rcases (show (Fin.appendEquiv 0 (n + p) '' Q i).IsRationalPolytope
        from by simpa [is_mixed_rational_polytope] using hQ i) with ⟨t, v, hv⟩
    refine ⟨t, fun a l ↦ v a (Fin.cast (by simp) l), ?_⟩
    unfold Qflat
    rw [hv]
    have hrange :
        dropZero '' (Set.range fun a : Fin t ↦ fun j : Fin (0 + (n + p)) ↦ (v a j : ℝ)) =
          Set.range fun a : Fin t ↦ fun l : Fin (n + p) ↦ (v a (Fin.cast (by simp) l) : ℝ) := by
      ext u
      constructor
      · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨(fun j : Fin (0 + (n + p)) ↦ (v a j : ℝ)), ⟨a, rfl⟩, rfl⟩
    calc
      dropZero '' convexHull ℝ (Set.range fun a : Fin t ↦ fun j : Fin (0 + (n + p)) ↦ (v a j : ℝ))
          = convexHull ℝ
              (dropZero '' Set.range fun a : Fin t ↦ fun j : Fin (0 + (n + p)) ↦ (v a j : ℝ)) := by
                simpa using
                  (hdropZeroLinear.image_convexHull
                    (Set.range fun a : Fin t ↦ fun j : Fin (0 + (n + p)) ↦ (v a j : ℝ)))
      _ = convexHull ℝ
            (Set.range fun a : Fin t ↦ fun l : Fin (n + p) ↦ (v a (Fin.cast (by simp) l) : ℝ)) := by
            rw [hrange]
  have hPflat_zero :
      rational_matrix_polyhedron A b =
        (⋃ i : Fin k, Qflat i) + integral_intcone (fun j : Fin q ↦ (r j).2) := by
    have hdropZero_append :
        ∀ xy : MixedRealPoint 0 (n + p), dropZero (Fin.appendEquiv 0 (n + p) xy) = xy.2 := by
      intro xy
      simpa [dropZero] using appendEquiv_zero_left_drop (xy := xy)
    have hdropZero_decomp :
        dropZero '' (Fin.appendEquiv 0 (n + p) '' ((⋃ i : Fin k, Q i) + mixed_integer_intcone r)) =
          (⋃ i : Fin k, Qflat i) + integral_intcone (fun j : Fin q ↦ (r j).2) := by
      have hImage :
          Fin.appendEquiv 0 (n + p) '' ((⋃ i : Fin k, Q i) + mixed_integer_intcone r) =
            (⋃ i : Fin k, Fin.appendEquiv 0 (n + p) '' Q i) +
              integral_intcone (fun j : Fin q ↦ Fin.append (r j).1 (r j).2) := by
        exact
          appendEquiv_image_iUnion_add_mixed_integer_intcone
            (n := 0) (p := n + p) Q r
      rw [hImage]
      ext u
      constructor
      · rintro ⟨w, hw, rfl⟩
        rcases hw with ⟨a, ha, b', hb', rfl⟩
        rcases Set.mem_iUnion.1 ha with ⟨i, hai⟩
        refine Set.mem_add.2 ⟨dropZero a, ?_, dropZero b', ?_, ?_⟩
        · exact Set.mem_iUnion.2 ⟨i, ⟨a, hai, rfl⟩⟩
        · rcases hb' with ⟨μ, rfl⟩
          refine (mem_integral_intcone_iff).2 ⟨μ, ?_⟩
          ext l
          have hsum :
              ∑ x : Fin q, (μ x : ℝ) *
                  ((((Fin.append (r x).1 (r x).2) (Fin.cast (by simp) l) : ℤ) : ℝ)) =
                ∑ x : Fin q, (μ x : ℝ) * (((r x).2 l : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have happ :
                ((Fin.append (r x).1 (r x).2) (Fin.cast (by simp) l) : ℤ) = (r x).2 l := by
              simpa [Fin.cast_natAdd] using Fin.append_right (r x).1 (r x).2 l
            simp [happ]
          simpa only [dropZero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hsum
        · rfl
      · rintro ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        rcases Set.mem_iUnion.1 hu₁ with ⟨i, hu₁⟩
        rcases hu₁ with ⟨a, ha, rfl⟩
        rcases hu₂ with ⟨μ, hμ⟩
        refine ⟨a + ∑ j : Fin q, (μ j : ℝ) •
          (fun l : Fin (0 + (n + p)) ↦ (((Fin.append (r j).1 (r j).2) l : ℤ) : ℝ)), ?_, ?_⟩
        · refine Set.mem_add.2 ⟨a, Set.mem_iUnion.2 ⟨i, ha⟩, ?_, ?_, ?_⟩
          · exact ∑ j : Fin q, (μ j : ℝ) •
              (fun l : Fin (0 + (n + p)) ↦ (((Fin.append (r j).1 (r j).2) l : ℤ) : ℝ))
          · exact (mem_integral_intcone_iff).2 ⟨μ, rfl⟩
          · rfl
        · ext l
          have hsum :
              ∑ x : Fin q, (μ x : ℝ) *
                  ((((Fin.append (r x).1 (r x).2) (Fin.cast (by simp) l) : ℤ) : ℝ)) =
                ∑ x : Fin q, (μ x : ℝ) * (((r x).2 l : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have happ :
                ((Fin.append (r x).1 (r x).2) (Fin.cast (by simp) l) : ℤ) = (r x).2 l := by
              simpa [Fin.cast_natAdd] using Fin.append_right (r x).1 (r x).2 l
            simp [happ]
          have hsum' :
              a (Fin.cast (by simp) l) +
                  ∑ x : Fin q, (μ x : ℝ) *
                    ((((Fin.append (r x).1 (r x).2) (Fin.cast (by simp) l) : ℤ) : ℝ)) =
                a (Fin.cast (by simp) l) +
                  ∑ x : Fin q, (μ x : ℝ) * (((r x).2 l : ℤ) : ℝ) := by
            exact congrArg (fun t : ℝ ↦ a (Fin.cast (by simp) l) + t) hsum
          simpa only [dropZero, Pi.add_apply, hμ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            using hsum'
    calc
      rational_matrix_polyhedron A b = dropZero '' (Fin.appendEquiv 0 (n + p) '' Pzero) := by
        ext u
        constructor
        · intro hu
          refine ⟨Fin.appendEquiv 0 (n + p) (fun i : Fin 0 ↦ Fin.elim0 i, u), ?_, ?_⟩
          · exact ⟨(fun i : Fin 0 ↦ Fin.elim0 i, u), by
              simpa [Pzero, rational_mixed_polyhedron, rational_matrix_polyhedron] using hu, rfl⟩
          · simp [dropZero, Fin.appendEquiv]
        · intro hu
          rcases hu with ⟨w, hw, hwu⟩
          rcases hw with ⟨xy, hxy, rfl⟩
          have hxy2 : xy.2 = u := by
            simpa [hdropZero_append xy] using hwu
          have hxy' : A.map (Rat.castHom ℝ) *ᵥ u ≤ fun i ↦ (b i : ℝ) := by
            simpa [hxy2, Pzero, rational_mixed_polyhedron, rational_matrix_polyhedron] using hxy
          simpa [rational_matrix_polyhedron] using hxy'
      _ = dropZero '' (Fin.appendEquiv 0 (n + p) '' ((⋃ i : Fin k, Q i) + mixed_integer_intcone r)) := by
            rw [hPzero_repr]
      _ = (⋃ i : Fin k, Qflat i) +
            integral_intcone (fun j : Fin q ↦ (r j).2) := by
            exact hdropZero_decomp
  have hPflat_decomp :
      (Fin.appendEquiv n p '' P) =
        (⋃ i : Fin k, Qflat i) +
          integral_intcone (fun j : Fin q ↦ (r j).2) := by
    calc
      (Fin.appendEquiv n p '' P) = rational_matrix_polyhedron A b := by
        simpa [rational_matrix_polyhedron] using hPflat_eq
      _ = (⋃ i : Fin k, Qflat i) +
            integral_intcone (fun j : Fin q ↦ (r j).2) := hPflat_zero
  exact ⟨k, q, Qflat, fun j ↦ (r j).2, hQflat, hPflat_decomp⟩

/-- Theorem 4.30 (1) (Meyer [276]). If `P ⊆ ℝ^n × ℝ^p` is a rational mixed polyhedron and
`S = mixed_integer_points P`, then `conv(S)` is again a rational mixed polyhedron. -/
theorem mixed_integer_hull_is_rational_mixed_polyhedron
    (P : Set (MixedRealPoint n p))
    (hP : is_rational_mixed_polyhedron P) :
    is_rational_mixed_polyhedron (convexHull ℝ (mixed_integer_points P)) := by
  -- The source proof works on the flattened set in `ℝ^(n + p)`.
  change is_rational_polyhedron ((Fin.appendEquiv n p) '' convexHull ℝ (mixed_integer_points P))
  rw [appendEquiv_image_convexHull]
  -- Route correction: split off the empty case first so the remaining blocker is only the
  -- nonempty Meyer truncation argument in flattened coordinates.
  by_cases hS_nonempty : Set.Nonempty (mixed_integer_points P)
  · rcases mixed_integer_points_eq_iUnion_rational_polytopes_add_intcone
        (P := P) hP with ⟨k, q, P', r, hP', hS_repr⟩
    let U : Set (Fin (n + p) → ℝ) := ⋃ i : Fin k, Fin.appendEquiv n p '' P' i
    let raysInt : Fin q → Fin (n + p) → ℤ := fun j ↦ Fin.append (r j).1 (r j).2
    have hS_flat :
        (Fin.appendEquiv n p '' mixed_integer_points P) = U + integral_intcone raysInt := by
      calc
        (Fin.appendEquiv n p '' mixed_integer_points P)
            = Fin.appendEquiv n p '' ((⋃ i : Fin k, P' i) + mixed_integer_intcone r) := by
                rw [hS_repr]
        _ = U + integral_intcone raysInt := by
              simpa [U, raysInt] using
                appendEquiv_image_iUnion_add_mixed_integer_intcone
                  (n := n) (p := p) P' r
    have hU_rational :
        (convexHull ℝ U).IsRationalPolytope := by
      refine convexHull_iUnion_isRationalPolytope
        (Q := fun i : Fin k ↦ Fin.appendEquiv n p '' P' i) ?_
      intro i
      simpa [U, is_mixed_rational_polytope] using hP' i
    rcases hU_rational with ⟨t, vertices, hvertices⟩
    let raysQ : Fin q → Fin (n + p) → ℚ := fun j i ↦ (raysInt j i : ℚ)
    let L : ℕ :=
      max
        ((Finset.univ : Finset (Fin t)).sup fun i ↦ EncodingSize.rationalVector (vertices i))
        ((Finset.univ : Finset (Fin q)).sup fun j ↦ EncodingSize.rationalVector (raysQ j))
    have hvertices_bound :
        ∀ i : Fin t, EncodingSize.rationalVector (vertices i) ≤ L := by
      intro i
      have hi :
          EncodingSize.rationalVector (vertices i) ≤
            (Finset.univ : Finset (Fin t)).sup
              (fun j ↦ EncodingSize.rationalVector (vertices j)) :=
        by simpa using
          (Finset.le_sup (s := (Finset.univ : Finset (Fin t)))
            (f := fun j ↦ EncodingSize.rationalVector (vertices j))
            (b := i)
            (by simp))
      exact le_trans hi (Nat.le_max_left _ _)
    have hrays_bound :
        ∀ j : Fin q, EncodingSize.rationalVector (raysQ j) ≤ L := by
      intro j
      have hj :
          EncodingSize.rationalVector (raysQ j) ≤
            (Finset.univ : Finset (Fin q)).sup
              (fun t ↦ EncodingSize.rationalVector (raysQ t)) :=
        by simpa using
          (Finset.le_sup (s := (Finset.univ : Finset (Fin q)))
            (f := fun t ↦ EncodingSize.rationalVector (raysQ t))
            (b := j)
            (by simp))
      exact le_trans hj (Nat.le_max_right _ _)
    rcases exists_rational_matrix_polyhedron_of_bounded_rational_vrepresentation_encoding
        vertices raysQ L hvertices_bound hrays_bound with
      ⟨π, m, A, b, hrepr, _, _⟩
    refine ⟨m, A, b, ?_⟩
    calc
      convexHull ℝ (Fin.appendEquiv n p '' mixed_integer_points P)
          = convexHull ℝ (U + integral_intcone raysInt) := by rw [hS_flat]
      _ = convexHull ℝ U + convexHull ℝ (integral_intcone raysInt) := by
            rw [convexHull_add]
      _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin (n + p) ↦ (vertices i u : ℝ)) +
            convexHull ℝ (integral_intcone raysInt) := by
              rw [hvertices]
      _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin (n + p) ↦ (vertices i u : ℝ)) +
            finitely_generated_cone
              (fun j : Fin q ↦ fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) := by
              rw [convexHull_integral_intcone_eq_finitely_generated_cone]
      _ = rational_matrix_polyhedron A b := by
            simpa [raysQ, raysInt, finitely_generated_cone] using hrepr
  · have hS_empty : mixed_integer_points P = ∅ := Set.not_nonempty_iff_eq_empty.mp hS_nonempty
    -- The empty mixed-integer hull is handled by an explicit rational witness for `∅`.
    simpa [hS_empty] using (is_rational_polyhedron_empty (k := n + p))

/-- Source-facing expansion of Theorem 4.30 (1): the rational mixed-integer hull admits a rational
matrix presentation. -/
theorem exists_rational_mixed_integer_hull
    (P : Set (MixedRealPoint n p))
    (hP : is_rational_mixed_polyhedron P) :
    ∃ m : ℕ,
      ∃ A : Matrix (Fin m) (Fin n) ℚ,
        ∃ G : Matrix (Fin m) (Fin p) ℚ,
          ∃ b : Fin m → ℚ,
            convexHull ℝ (mixed_integer_points P) = rational_mixed_polyhedron A G b := by
  simpa [is_rational_mixed_polyhedron_iff] using
    mixed_integer_hull_is_rational_mixed_polyhedron P hP

/-- Companion to Theorem 4.30 (2) (Meyer [276]). If `P ⊆ ℝ^n × ℝ^p` is a rational mixed polyhedron and
`S = mixed_integer_points P` is nonempty, then `conv(S)` and `P` have the same recession cone. -/
theorem mixed_integer_hull_recessionCone_eq
    (P : Set (MixedRealPoint n p))
    (hP : is_rational_mixed_polyhedron P)
    (hS_nonempty : Set.Nonempty (mixed_integer_points P)) :
    recessionCone (convexHull ℝ (mixed_integer_points P)) = recessionCone P := by
  let Sflat : Set (Fin (n + p) → ℝ) := (Fin.appendEquiv n p) '' mixed_integer_points P
  let Pflat : Set (Fin (n + p) → ℝ) := (Fin.appendEquiv n p) '' P
  rcases hS_nonempty with ⟨xy₀, hxy₀⟩
  let x₀ : Fin (n + p) → ℝ := Fin.appendEquiv n p xy₀
  have hx₀Sflat : x₀ ∈ Sflat := by
    exact ⟨xy₀, hxy₀, rfl⟩
  have hx₀Pflat : x₀ ∈ Pflat := flattened_mixed_integer_points_subset hx₀Sflat
  have hx₀Int :
      (fun i : Fin n ↦ x₀ (Fin.castAdd p i)) ∈ integerVectors n := by
    exact (mem_flattened_mixed_integer_points_iff (P := P) (u := x₀)).1 hx₀Sflat |>.2
  rcases exists_flattened_recession_system (P := P) hP ⟨xy₀, hxy₀⟩ with
    ⟨mP, AP, bP, hPflat_eq, -⟩
  have hPflat_nonempty :
      Set.Nonempty (polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ))) := by
    have hx : x₀ ∈ (Fin.appendEquiv n p '' P) := by
      simpa [Pflat] using hx₀Pflat
    rw [hPflat_eq] at hx
    exact ⟨x₀, hx⟩
  rcases mixed_integer_points_eq_iUnion_rational_polytopes_add_intcone
      (P := P) hP with ⟨k, q, P', r, hP', hS_repr⟩
  let U : Set (Fin (n + p) → ℝ) := ⋃ i : Fin k, (Fin.appendEquiv n p) '' P' i
  let raysInt : Fin q → Fin (n + p) → ℤ := fun j ↦ Fin.append (r j).1 (r j).2
  have hSflat :
      Sflat = U + integral_intcone raysInt := by
    have hSflat_image :
        Sflat = (Fin.appendEquiv n p) '' ((⋃ i : Fin k, P' i) + mixed_integer_intcone r) := by
      simpa [Sflat] using congrArg (fun T ↦ (Fin.appendEquiv n p) '' T) hS_repr
    calc
      Sflat = (Fin.appendEquiv n p) '' ((⋃ i : Fin k, P' i) + mixed_integer_intcone r) := hSflat_image
      _ = U + integral_intcone raysInt := by
            simpa [Sflat, U, raysInt] using
              appendEquiv_image_iUnion_add_mixed_integer_intcone (n := n) (p := p) P' r
  have hU_rational :
      (convexHull ℝ U).IsRationalPolytope := by
    refine convexHull_iUnion_isRationalPolytope
      (Q := fun i : Fin k ↦ (Fin.appendEquiv n p) '' P' i) ?_
    intro i
    simpa [is_mixed_rational_polytope] using hP' i
  rcases hU_rational with ⟨t, vertices, hvertices⟩
  have hHull_rational :
      is_rational_polyhedron (convexHull ℝ Sflat) := by
    simpa [is_rational_mixed_polyhedron, Sflat, appendEquiv_image_convexHull] using
      mixed_integer_hull_is_rational_mixed_polyhedron (n := n) (p := p) P hP
  rcases hHull_rational with ⟨mH, AH, bH, hHull_eq⟩
  have hHull_nonempty :
      Set.Nonempty (polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ))) := by
    have hx : x₀ ∈ convexHull ℝ Sflat := subset_convexHull ℝ Sflat hx₀Sflat
    rw [hHull_eq] at hx
    exact ⟨x₀, hx⟩
  have hHull_eq_poly :
      convexHull ℝ Sflat = polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ)) := by
    simpa [Sflat] using hHull_eq
  have hPflat_eq_poly :
      Pflat = polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ)) := by
    simpa [Pflat] using hPflat_eq
  have hHull_repr :
      polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ)) =
        convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin (n + p) ↦ (vertices i u : ℝ)) +
          finitely_generated_cone
            (fun j : Fin q ↦ fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) := by
    calc
      polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ))
          = convexHull ℝ Sflat := by rw [hHull_eq]
      _ = convexHull ℝ (U + integral_intcone raysInt) := by rw [hSflat]
      _ = convexHull ℝ U + convexHull ℝ (integral_intcone raysInt) := by
            rw [convexHull_add]
      _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin (n + p) ↦ (vertices i u : ℝ)) +
            convexHull ℝ (integral_intcone raysInt) := by
              rw [hvertices]
      _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin (n + p) ↦ (vertices i u : ℝ)) +
            finitely_generated_cone
              (fun j : Fin q ↦ fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) := by
              rw [convexHull_integral_intcone_eq_finitely_generated_cone]
  have hHull_rec :
      recessionCone (convexHull ℝ Sflat) =
        closure
          (finitely_generated_cone
            (fun j : Fin q ↦ fun u : Fin (n + p) ↦ (raysInt j u : ℝ))) := by
    calc
      recessionCone (convexHull ℝ Sflat)
          = recessionCone
              (polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ))) := by
                rw [hHull_eq_poly]
      _ = closure
            (finitely_generated_cone
              (fun j : Fin q ↦ fun u : Fin (n + p) ↦ (raysInt j u : ℝ))) := by
            exact
              recessionCone_eq_finitely_generated_cone_of_polyhedron_repr
                (AH.map (Rat.castHom ℝ))
                (fun i ↦ (bH i : ℝ))
                (fun i : Fin t ↦ fun u : Fin (n + p) ↦ (vertices i u : ℝ))
                (fun j : Fin q ↦ fun u : Fin (n + p) ↦ (raysInt j u : ℝ))
                hHull_nonempty
                hHull_repr
  have hraysInt_mem_Pflat :
      ∀ j : Fin q,
        (fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) ∈ recessionCone Pflat := by
    intro j
    rcases Set.mem_add.1 (by simpa [hSflat] using hx₀Sflat) with ⟨u₀, hu₀, c₀, hc₀, hx₀_eq⟩
    have hx₀_poly :
        x₀ ∈ polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ)) := by
      have hx : x₀ ∈ (Fin.appendEquiv n p '' P) := by
        simpa [Pflat] using hx₀Pflat
      rw [hPflat_eq] at hx
      exact hx
    have htranslate :
        ∀ t : ℕ,
          x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) ∈
            polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ)) := by
      intro t
      have hc₀' :
          c₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) ∈ integral_intcone raysInt := by
        exact
          add_mem_integral_intcone
            hc₀
            (nat_smul_generator_mem_integral_intcone raysInt j t)
      have hx_translate :
          x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) ∈ U + integral_intcone raysInt := by
        refine Set.mem_add.2 ⟨u₀, hu₀, c₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysInt j u : ℝ)),
          hc₀', ?_⟩
        rw [← hx₀_eq]
        simpa [add_assoc]
      have hx_translate_Sflat :
          x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) ∈ Sflat := by
        simpa [hSflat] using hx_translate
      have hx_translate_Pflat :
          x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) ∈ Pflat :=
        flattened_mixed_integer_points_subset (P := P) hx_translate_Sflat
      have hx : x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) ∈ (Fin.appendEquiv n p '' P) := by
        simpa [Pflat] using hx_translate_Pflat
      rw [hPflat_eq] at hx
      exact hx
    have hrec_poly :
        (fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) ∈
          recessionCone (polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ))) := by
      exact
        mem_recessionCone_of_natTranslateMem
          (AP.map (Rat.castHom ℝ))
          (fun i ↦ (bP i : ℝ))
          hx₀_poly
          htranslate
    have hrec_image :
        (fun u : Fin (n + p) ↦ (raysInt j u : ℝ)) ∈ recessionCone ((Fin.appendEquiv n p) '' P) := by
      rw [hPflat_eq]
      exact hrec_poly
    simpa [Pflat] using hrec_image
  have hHull_subset_Pflat :
      recessionCone (convexHull ℝ Sflat) ⊆ recessionCone Pflat := by
    have hPflat_rec_closed : IsClosed (recessionCone Pflat) := by
      rw [hPflat_eq_poly]
      exact
        isClosed_recessionCone_polyhedron_local
          (AP.map (Rat.castHom ℝ))
          (fun i ↦ (bP i : ℝ))
          hPflat_nonempty
    rw [hHull_rec]
    exact
      closure_minimal
        (finitelyGeneratedCone_subset_recessionCone_of_generator_mem hraysInt_mem_Pflat)
        hPflat_rec_closed
  rcases exists_flattened_ambient_integral_decomposition (P := P) hP with
    ⟨kP, qP, Qflat, raysP, hQflat, hPflat_decomp⟩
  have hQflat_rational :
      (convexHull ℝ (⋃ i : Fin kP, Qflat i)).IsRationalPolytope := by
    exact convexHull_iUnion_isRationalPolytope Qflat hQflat
  rcases hQflat_rational with ⟨tP, verticesP, hverticesP⟩
  have hPflat_decomp_eq :
      Pflat = (⋃ i : Fin kP, Qflat i) + integral_intcone raysP := by
    simpa [Pflat] using hPflat_decomp
  have hPflat_convex : Convex ℝ Pflat := by
    rw [hPflat_eq_poly]
    exact convex_polyhedron_le_set_local _ _
  have hPflat_repr :
      polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ)) =
        convexHull ℝ (Set.range fun i : Fin tP ↦ fun u : Fin (n + p) ↦ (verticesP i u : ℝ)) +
          finitely_generated_cone
            (fun j : Fin qP ↦ fun u : Fin (n + p) ↦ (raysP j u : ℝ)) := by
    have hdecomp_convex :
        Convex ℝ ((⋃ i : Fin kP, Qflat i) + integral_intcone raysP) := by
      simpa [hPflat_decomp_eq] using hPflat_convex
    calc
      polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ)) = Pflat := by
        exact hPflat_eq_poly.symm
      _ = (⋃ i : Fin kP, Qflat i) + integral_intcone raysP := hPflat_decomp_eq
      _ = convexHull ℝ ((⋃ i : Fin kP, Qflat i) + integral_intcone raysP) := by
            symm
            exact hdecomp_convex.convexHull_eq
      _ = convexHull ℝ (⋃ i : Fin kP, Qflat i) + convexHull ℝ (integral_intcone raysP) := by
            rw [convexHull_add]
      _ = convexHull ℝ (Set.range fun i : Fin tP ↦ fun u : Fin (n + p) ↦ (verticesP i u : ℝ)) +
            convexHull ℝ (integral_intcone raysP) := by
              rw [hverticesP]
      _ = convexHull ℝ (Set.range fun i : Fin tP ↦ fun u : Fin (n + p) ↦ (verticesP i u : ℝ)) +
            finitely_generated_cone
              (fun j : Fin qP ↦ fun u : Fin (n + p) ↦ (raysP j u : ℝ)) := by
              rw [convexHull_integral_intcone_eq_finitely_generated_cone]
  have hP_rec :
      recessionCone Pflat =
        closure
          (finitely_generated_cone
            (fun j : Fin qP ↦ fun u : Fin (n + p) ↦ (raysP j u : ℝ))) := by
    calc
      recessionCone Pflat
          = recessionCone
              (polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ))) := by
                rw [hPflat_eq_poly]
      _ = closure
            (finitely_generated_cone
              (fun j : Fin qP ↦ fun u : Fin (n + p) ↦ (raysP j u : ℝ))) := by
            exact
              recessionCone_eq_finitely_generated_cone_of_polyhedron_repr
                (AP.map (Rat.castHom ℝ))
                (fun i ↦ (bP i : ℝ))
                (fun i : Fin tP ↦ fun u : Fin (n + p) ↦ (verticesP i u : ℝ))
                (fun j : Fin qP ↦ fun u : Fin (n + p) ↦ (raysP j u : ℝ))
                hPflat_nonempty
                hPflat_repr
  have hraysP_mem_hull :
      ∀ j : Fin qP,
        (fun u : Fin (n + p) ↦ (raysP j u : ℝ)) ∈ recessionCone (convexHull ℝ Sflat) := by
    intro j
    have hjP :
        (fun u : Fin (n + p) ↦ (raysP j u : ℝ)) ∈ recessionCone Pflat := by
      rw [hP_rec]
      exact subset_closure <|
        (mem_finitely_generated_cone_iff).2 <|
          ⟨Pi.single j 1, by
            intro t
            by_cases ht : t = j
            · subst ht
              simp
            · simp [ht], by
            ext u
            rw [Finset.sum_eq_single j]
            · simp
            · intro t _ ht
              simp [ht]
            · simp⟩
    have hx₀_hull_poly :
        x₀ ∈ polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ)) := by
      have hx : x₀ ∈ convexHull ℝ Sflat := subset_convexHull ℝ Sflat hx₀Sflat
      rw [hHull_eq] at hx
      exact hx
    have htranslate :
        ∀ t : ℕ,
          x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysP j u : ℝ)) ∈
            polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ)) := by
      intro t
      have hP_translate :
          x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysP j u : ℝ)) ∈ Pflat := by
        rw [mem_recessionCone_iff] at hjP
        exact hjP hx₀Pflat t (by positivity)
      have hInt_translate :
          (fun i : Fin n ↦
            (x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysP j u : ℝ))) (Fin.castAdd p i)) ∈
              integerVectors n := by
        simpa [Pi.add_apply, Pi.smul_apply, mul_comm, add_comm, add_left_comm, add_assoc] using
          integerVectors_add_nat_smul_of_integral
            hx₀Int
            (fun i : Fin n ↦ raysP j (Fin.castAdd p i))
            t
      have hS_translate :
          x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysP j u : ℝ)) ∈ Sflat := by
        exact
          (mem_flattened_mixed_integer_points_iff
            (P := P)
            (u := x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysP j u : ℝ)))).2
            ⟨hP_translate, hInt_translate⟩
      have hx : x₀ + (t : ℝ) • (fun u : Fin (n + p) ↦ (raysP j u : ℝ)) ∈ convexHull ℝ Sflat :=
        subset_convexHull ℝ Sflat hS_translate
      rw [hHull_eq] at hx
      exact hx
    have hrec_poly :
        (fun u : Fin (n + p) ↦ (raysP j u : ℝ)) ∈
          recessionCone (polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ))) := by
      exact
        mem_recessionCone_of_natTranslateMem
          (AH.map (Rat.castHom ℝ))
          (fun i ↦ (bH i : ℝ))
          hx₀_hull_poly
          htranslate
    rw [hHull_eq_poly]
    exact hrec_poly
  have hPflat_subset_hull :
      recessionCone Pflat ⊆ recessionCone (convexHull ℝ Sflat) := by
    have hHull_rec_closed : IsClosed (recessionCone (convexHull ℝ Sflat)) := by
      rw [hHull_eq_poly]
      exact
        isClosed_recessionCone_polyhedron_local
          (AH.map (Rat.castHom ℝ))
          (fun i ↦ (bH i : ℝ))
          hHull_nonempty
    rw [hP_rec]
    exact
      closure_minimal
        (finitelyGeneratedCone_subset_recessionCone_of_generator_mem hraysP_mem_hull)
        hHull_rec_closed
  have hflat :
      recessionCone (convexHull ℝ Sflat) = recessionCone Pflat :=
    Set.Subset.antisymm hHull_subset_Pflat hPflat_subset_hull
  ext d
  constructor
  · intro hd
    have hdFlat :
        Fin.appendEquiv n p d ∈
          recessionCone ((Fin.appendEquiv n p) '' convexHull ℝ (mixed_integer_points P)) := by
      exact
        (mem_recessionCone_flatten_iff
          (Q := convexHull ℝ (mixed_integer_points P))
          (d := d)).2 hd
    rw [appendEquiv_image_convexHull, hflat] at hdFlat
    exact (mem_recessionCone_flatten_iff (Q := P) (d := d)).1 hdFlat
  · intro hd
    have hdFlat :
        Fin.appendEquiv n p d ∈ recessionCone Pflat := by
      exact (mem_recessionCone_flatten_iff (Q := P) (d := d)).2 hd
    have hdFlat' :
        Fin.appendEquiv n p d ∈
          recessionCone ((Fin.appendEquiv n p) '' convexHull ℝ (mixed_integer_points P)) := by
      rw [appendEquiv_image_convexHull, hflat]
      exact hdFlat
    exact
      (mem_recessionCone_flatten_iff
        (Q := convexHull ℝ (mixed_integer_points P))
        (d := d)).1 hdFlat'

end Theorem430
