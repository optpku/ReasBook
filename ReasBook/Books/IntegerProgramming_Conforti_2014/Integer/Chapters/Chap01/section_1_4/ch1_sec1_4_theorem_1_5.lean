import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_13.ch3_sec3_13_theorem_3_39
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_theorem_4_30.Decomposition
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_2.ch4_sec4_8_2_lemma_4_35
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic

open scoped BigOperators Matrix Pointwise

section Theorem15

variable {m n p : ℕ}

/-- Helper for Theorem 1.5: the augmented integer-block matrix adds the nonnegativity rows
`-I x ≤ 0` below the original mixed system. -/
private def nonnegativeRationalMixedWitnessA
    (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin (m + (n + p))) (Fin n) ℚ :=
  fun i ↦
    Fin.addCases
      A
      (Fin.addCases
        (fun i' j ↦ if j = i' then -1 else 0)
        (fun _ _ ↦ 0))
      i

/-- Helper for Theorem 1.5: the augmented continuous-block matrix adds the nonnegativity rows
`-I y ≤ 0` below the original mixed system. -/
private def nonnegativeRationalMixedWitnessG
    (G : Matrix (Fin m) (Fin p) ℚ) :
    Matrix (Fin (m + (n + p))) (Fin p) ℚ :=
  fun i ↦
    Fin.addCases
      G
      (Fin.addCases
        (fun _ _ ↦ 0)
        (fun i' j ↦ if j = i' then -1 else 0))
      i

/-- Helper for Theorem 1.5: the augmented right-hand side appends zeros for the nonnegativity
rows. -/
private def nonnegativeRationalMixedWitnessRhs
    (b : Fin m → ℚ) :
    Fin (m + (n + p)) → ℚ :=
  Fin.addCases b (Fin.addCases (fun _ ↦ 0) (fun _ ↦ 0))

/-- Helper for Theorem 1.5: the augmented witness inequalities are exactly the original mixed
system together with the coordinatewise nonnegativity constraints. -/
private theorem nonnegativeRationalMixedWitness_le_iff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ)
    (xy : MixedRealPoint n p) :
    (((nonnegativeRationalMixedWitnessA A).map (Rat.castHom ℝ)) *ᵥ xy.1 +
        ((nonnegativeRationalMixedWitnessG G).map (Rat.castHom ℝ)) *ᵥ xy.2 ≤
      fun i ↦ (nonnegativeRationalMixedWitnessRhs b i : ℝ)) ↔
      ((A.map (Rat.castHom ℝ)) *ᵥ xy.1 + (G.map (Rat.castHom ℝ)) *ᵥ xy.2 ≤
          fun i ↦ (b i : ℝ)) ∧
        0 ≤ xy.1 ∧ 0 ≤ xy.2 := by
  constructor
  · intro hxy
    refine ⟨?_, ?_, ?_⟩
    · intro i
      -- Restrict the augmented system to its leading block to recover `A x + G y ≤ b`.
      have hrow := hxy (Fin.castAdd (n + p) i)
      simpa [nonnegativeRationalMixedWitnessA, nonnegativeRationalMixedWitnessG,
        nonnegativeRationalMixedWitnessRhs, Matrix.mulVec, dotProduct] using hrow
    · intro j
      -- The first auxiliary block is the row `-x j ≤ 0`.
      have hrow := hxy (Fin.natAdd m (Fin.castAdd p j))
      have hsum :
          ∑ x : Fin n, (((if x = j then (-1 : ℚ) else 0 : ℚ) : ℝ) * xy.1 x) = -xy.1 j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro x _ hx
          simp [hx]
        · simp
      exact neg_nonpos.mp <| by
        simpa [nonnegativeRationalMixedWitnessA, nonnegativeRationalMixedWitnessG,
          nonnegativeRationalMixedWitnessRhs, Matrix.mulVec, dotProduct, hsum] using hrow
    · intro j
      -- The second auxiliary block is the row `-y j ≤ 0`.
      have hrow := hxy (Fin.natAdd m (Fin.natAdd n j))
      have hsum :
          ∑ x : Fin p, (((if x = j then (-1 : ℚ) else 0 : ℚ) : ℝ) * xy.2 x) = -xy.2 j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro x _ hx
          simp [hx]
        · simp
      exact neg_nonpos.mp <| by
        simpa [nonnegativeRationalMixedWitnessA, nonnegativeRationalMixedWitnessG,
          nonnegativeRationalMixedWitnessRhs, Matrix.mulVec, dotProduct, hsum] using hrow
  · rintro ⟨hineq, hx_nonneg, hy_nonneg⟩
    intro row
    refine Fin.addCases ?_ ?_ row
    · intro i
      -- The original rows come directly from `hineq`.
      simpa [nonnegativeRationalMixedWitnessA, nonnegativeRationalMixedWitnessG,
        nonnegativeRationalMixedWitnessRhs, Matrix.mulVec, dotProduct] using hineq i
    · refine Fin.addCases ?_ ?_
      · intro j
        -- The appended `x`-block rows encode `0 ≤ xy.1`.
        have hsum :
            ∑ x : Fin n, (((if x = j then (-1 : ℚ) else 0 : ℚ) : ℝ) * xy.1 x) = -xy.1 j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro x _ hx
            simp [hx]
          · simp
        simpa [nonnegativeRationalMixedWitnessA, nonnegativeRationalMixedWitnessG,
          nonnegativeRationalMixedWitnessRhs, Matrix.mulVec, dotProduct, hsum] using
          (neg_nonpos.mpr (hx_nonneg j) : -xy.1 j ≤ 0)
      · intro j
        -- The appended `y`-block rows encode `0 ≤ xy.2`.
        have hsum :
            ∑ x : Fin p, (((if x = j then (-1 : ℚ) else 0 : ℚ) : ℝ) * xy.2 x) = -xy.2 j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro x _ hx
            simp [hx]
          · simp
        simpa [nonnegativeRationalMixedWitnessA, nonnegativeRationalMixedWitnessG,
          nonnegativeRationalMixedWitnessRhs, Matrix.mulVec, dotProduct, hsum] using
          (neg_nonpos.mpr (hy_nonneg j) : -xy.2 j ≤ 0)

/-- Helper for Theorem 1.5: the source-facing nonnegative mixed system is exactly one augmented
`rational_mixed_polyhedron` with the original rows followed by the `x ≥ 0` and `y ≥ 0` rows. -/
private theorem nonnegativeRationalMixedPolyhedron_eq_augmentedWitness
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) :
    nonnegative_rational_mixed_polyhedron A G b =
      rational_mixed_polyhedron
        (nonnegativeRationalMixedWitnessA A)
        (nonnegativeRationalMixedWitnessG G)
        (nonnegativeRationalMixedWitnessRhs b) := by
  ext xy
  -- Unfold the source-facing set-builder and rewrite the augmented witness once.
  simpa [nonnegative_rational_mixed_polyhedron, mem_rational_mixed_polyhedron_iff] using
    (nonnegativeRationalMixedWitness_le_iff A G b xy).symm

/-- The nonnegative rational mixed system
`A x + G y ≤ b`, `x ≥ 0`, `y ≥ 0` is a rational mixed polyhedron. -/
theorem nonnegative_rational_mixed_polyhedron_is_rational_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) :
    is_rational_mixed_polyhedron (nonnegative_rational_mixed_polyhedron A G b) := by
  -- Route correction: keep the proof in the mixed owner and append the nonnegativity rows
  -- directly, instead of flattening through `Fin.appendEquiv` and transporting to an ordinary
  -- matrix polyhedron.
  refine (is_rational_mixed_polyhedron_iff).2 ?_
  refine ⟨m + (n + p), nonnegativeRationalMixedWitnessA A, nonnegativeRationalMixedWitnessG G,
    nonnegativeRationalMixedWitnessRhs b, ?_⟩
  exact nonnegativeRationalMixedPolyhedron_eq_augmentedWitness A G b

/-- Membership in `nonnegative_rational_mixed_polyhedron A G b` means satisfying the rational
mixed system `A x + G y ≤ b` together with the nonnegativity constraints on both coordinate
blocks. -/
theorem mem_nonnegative_rational_mixed_polyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ}
    {xy : MixedRealPoint n p} :
    xy ∈ nonnegative_rational_mixed_polyhedron A G b ↔
      ((A.map (Rat.castHom ℝ)) *ᵥ xy.1 + (G.map (Rat.castHom ℝ)) *ᵥ xy.2 ≤
          fun i ↦ (b i : ℝ)) ∧
        0 ≤ xy.1 ∧ 0 ≤ xy.2 := by
  -- Unfold the source-facing owner; the remaining statement is exactly its defining conjunction.
  simp [nonnegative_rational_mixed_polyhedron, mem_rational_mixed_polyhedron_iff]

/-- Membership in `nonnegative_rational_mixed_integer_points A G b` means satisfying the rational
mixed system `A x + G y ≤ b`, the nonnegativity constraints, and integrality of the `x`-block. -/
theorem mem_nonnegative_rational_mixed_integer_points_iff
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ}
    {xy : MixedRealPoint n p} :
    xy ∈ nonnegative_rational_mixed_integer_points A G b ↔
      ((A.map (Rat.castHom ℝ)) *ᵥ xy.1 + (G.map (Rat.castHom ℝ)) *ᵥ xy.2 ≤
          fun i ↦ (b i : ℝ)) ∧
        0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧ xy.1 ∈ integerVectors n := by
  rw [nonnegative_rational_mixed_integer_points, mem_mixed_integer_points_iff,
    mem_nonnegative_rational_mixed_polyhedron_iff, mem_mixed_integer_lattice_iff]
  constructor
  · rintro ⟨hPoly, hx_integer⟩
    exact ⟨hPoly.1, hPoly.2.1, hPoly.2.2, hx_integer⟩
  · rintro ⟨hMixed, hx_nonneg, hy_nonneg, hx_integer⟩
    exact ⟨⟨hMixed, hx_nonneg, hy_nonneg⟩, hx_integer⟩

namespace Theorem15Support

/-- Helper for Theorem 1.5: a flattened set is a rational polytope when it is the convex hull of
finitely many rational vertices. -/
def IsRationalPolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  ∃ k : ℕ,
    ∃ v : Fin k → Fin d → ℚ,
      P = convexHull ℝ (Set.range fun i : Fin k ↦ fun j : Fin d ↦ (v i j : ℝ))

/-- Helper for Theorem 1.5: flattening by `Fin.appendEquiv` is linear on mixed-space points. -/
lemma isLinearMap_appendEquiv :
    IsLinearMap ℝ (Fin.appendEquiv (α := ℝ) n p) := by
  refine ⟨?_, ?_⟩
  · intro x y
    -- Check additivity blockwise so the `Fin.append` coercions stay syntactic.
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]
  · intro a x
    -- Scalar multiplication is also blockwise on the two coordinate blocks.
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]

/-- Helper for Theorem 1.5: flattening commutes with convex hull because the flattening map is
linear. -/
lemma appendEquiv_image_convexHull
    (S : Set (MixedRealPoint n p)) :
    Fin.appendEquiv (α := ℝ) n p '' convexHull ℝ S =
      convexHull ℝ (Fin.appendEquiv (α := ℝ) n p '' S) := by
  -- Apply the linear-image theorem once at the canonical flattening map.
  simpa using (isLinearMap_appendEquiv (n := n) (p := p)).image_convexHull S

/-- Helper for Theorem 1.5: the empty set is a rational polyhedron. -/
lemma is_rational_polyhedron_empty
    {k : ℕ} :
    is_rational_polyhedron (∅ : Set (Fin k → ℝ)) := by
  -- The inconsistent single inequality `0 ≤ -1` cuts out exactly the empty set.
  refine ⟨1, 0, fun _ : Fin 1 ↦ (-1 : ℚ), ?_⟩
  ext x
  constructor
  · intro hx
    exact False.elim hx
  · intro hx
    have hx0 : (0 : ℝ) ≤ -1 := by
      simpa [polyhedron_le_set] using hx 0
    linarith

/-- Helper for Theorem 1.5: the local integral cone is the set of finite nonnegative integer
combinations of the integral rays `r`. -/
def integral_intcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) : Set (Fin k → ℝ) :=
  {u | ∃ a : Fin q → ℕ, u = ∑ j, (a j : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))}

/-- Helper for Theorem 1.5: membership in the local integral cone is exactly the defining finite
integer conic-combination formula. -/
theorem mem_integral_intcone_iff
    {k q : ℕ} {r : Fin q → Fin k → ℤ} {u : Fin k → ℝ} :
    u ∈ integral_intcone r ↔
      ∃ a : Fin q → ℕ, u = ∑ j, (a j : ℝ) • (fun i : Fin k ↦ (r j i : ℝ)) := by
  rfl

/-- Helper for Theorem 1.5: the zero vector belongs to every integral cone. -/
lemma zero_mem_integral_intcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) :
    (0 : Fin k → ℝ) ∈ integral_intcone r := by
  -- Choose the zero multiplicity vector.
  exact (mem_integral_intcone_iff).2 ⟨fun _ ↦ 0, by simp⟩

/-- Helper for Theorem 1.5: every listed generator belongs to its integral cone. -/
lemma generator_mem_integral_intcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (j : Fin q) :
    (fun i ↦ (r j i : ℝ)) ∈ integral_intcone r := by
  -- Use the coefficient vector that is `1` on the chosen ray and `0` elsewhere.
  refine (mem_integral_intcone_iff).2 ?_
  refine ⟨Pi.single j 1, ?_⟩
  classical
  ext i
  rw [Finset.sum_eq_single j]
  · simp
  · intro c _ hc
    ext i'
    simp [hc]
  · simp

/-- Helper for Theorem 1.5: the integral cone is closed under addition. -/
lemma add_mem_integral_intcone
    {k q : ℕ} {r : Fin q → Fin k → ℤ}
    {u v : Fin k → ℝ}
    (hu : u ∈ integral_intcone r)
    (hv : v ∈ integral_intcone r) :
    u + v ∈ integral_intcone r := by
  -- Add the coefficient vectors witnessing the two conic combinations.
  rcases (mem_integral_intcone_iff).1 hu with ⟨a, rfl⟩
  rcases (mem_integral_intcone_iff).1 hv with ⟨b, rfl⟩
  refine (mem_integral_intcone_iff).2 ?_
  refine ⟨fun j ↦ a j + b j, ?_⟩
  simp [Nat.cast_add, add_smul, Finset.sum_add_distrib]

/-- Helper for Theorem 1.5: truncating the last generator embeds the smaller integral cone into
the larger one. -/
lemma integral_intcone_castSucc_subset
    {k q : ℕ} (r : Fin (q + 1) → Fin k → ℤ) :
    integral_intcone (fun j : Fin q ↦ fun i : Fin k ↦ r j.castSucc i) ⊆
      integral_intcone r := by
  intro u hu
  rcases (mem_integral_intcone_iff).1 hu with ⟨a, ha⟩
  refine (mem_integral_intcone_iff).2 ?_
  let a' : Fin (q + 1) → ℕ := Fin.snoc a 0
  refine ⟨a', ?_⟩
  rw [ha]
  ext i
  rw [Fin.sum_univ_castSucc]
  simp [a', Fin.snoc_castSucc, Fin.snoc_last, add_comm]

/-- Helper for Theorem 1.5: translating the convex hull of the integral cone by another integral
cone element stays inside the same convex hull. -/
lemma add_mem_convexHull_integral_intcone
    {k q : ℕ} {r : Fin q → Fin k → ℤ}
    {u v : Fin k → ℝ}
    (hu : u ∈ convexHull ℝ (integral_intcone r))
    (hv : v ∈ integral_intcone r) :
    u + v ∈ convexHull ℝ (integral_intcone r) := by
  have htranslate_subset :
      v +ᵥ integral_intcone r ⊆ integral_intcone r := by
    -- Translate cone points by `v`; closure under addition keeps the result in the same cone.
    rintro w ⟨z, hz, rfl⟩
    simpa [Pi.vadd_def, vadd_eq_add, add_comm] using
      add_mem_integral_intcone (r := r) hv hz
  have htranslate_hull :
      v +ᵥ convexHull ℝ (integral_intcone r) ⊆ convexHull ℝ (integral_intcone r) := by
    -- Push the inclusion through `convexHull_vadd`.
    rw [← convexHull_vadd]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro w hw
    exact subset_convexHull ℝ _ (htranslate_subset hw)
  have huv :
      u + v ∈ v +ᵥ convexHull ℝ (integral_intcone r) := by
    refine ⟨u, hu, ?_⟩
    ext i
    simp [vadd_eq_add, add_comm]
  exact htranslate_hull huv

/-- Helper for Theorem 1.5: every fractional combination of the integral generators already lies
in the convex hull of their integral cone. -/
lemma fractional_combination_mem_convexHull_integral_intcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (μ : Fin q → ℝ)
    (hμ_nonneg : ∀ j : Fin q, 0 ≤ μ j)
    (hμ_le_one : ∀ j : Fin q, μ j ≤ 1) :
    (∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ))) ∈
      convexHull ℝ (integral_intcone r) := by
  induction q with
  | zero =>
      simpa using
        (subset_convexHull ℝ (integral_intcone r) (zero_mem_integral_intcone r))
  | succ q ih =>
      let rInit : Fin q → Fin k → ℤ := fun j i ↦ r j.castSucc i
      let μInit : Fin q → ℝ := fun j ↦ μ j.castSucc
      have hbase_small :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) ∈
            convexHull ℝ (integral_intcone rInit) := by
        exact ih rInit μInit (fun j ↦ hμ_nonneg j.castSucc) (fun j ↦ hμ_le_one j.castSucc)
      have hbase :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) ∈
            convexHull ℝ (integral_intcone r) := by
        -- First embed the smaller cone into the larger one, then lift the hull inclusion.
        refine convexHull_min ?_ (convex_convexHull ℝ _) hbase_small
        intro u hu
        exact subset_convexHull ℝ _ (integral_intcone_castSucc_subset (r := r) hu)
      let lastRay : Fin k → ℝ := fun i ↦ (r (Fin.last q) i : ℝ)
      have hbase_plus :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) + lastRay ∈
            convexHull ℝ (integral_intcone r) := by
        -- Add the last generator using the integral-cone translation lemma.
        exact add_mem_convexHull_integral_intcone
          (r := r) hbase (generator_mem_integral_intcone r (Fin.last q))
      have hlast :
          μ (Fin.last q) ∈ Set.Icc (0 : ℝ) 1 := ⟨hμ_nonneg _, hμ_le_one _⟩
      have hfinal :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) +
              μ (Fin.last q) • lastRay ∈
            convexHull ℝ (integral_intcone r) := by
        -- Convexity interpolates between the base point and its translate by the last ray.
        exact (convex_convexHull ℝ (integral_intcone r)).add_smul_mem hbase hbase_plus hlast
      simpa [rInit, μInit, lastRay, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        add_comm, add_left_comm, add_assoc] using hfinal

/-- Helper for Theorem 1.5: the convex hull of an integral cone is the corresponding real
finitely generated cone. -/
lemma convexHull_integral_intcone_eq_finitely_generated_cone
    {k q : ℕ}
    (r : Fin q → Fin k → ℤ) :
    convexHull ℝ (integral_intcone r) =
      finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)) := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ ?_
    · intro u hu
      rcases (mem_integral_intcone_iff).1 hu with ⟨a, rfl⟩
      refine (mem_finitely_generated_cone_iff).2 ?_
      refine ⟨fun j ↦ (a j : ℝ), ?_, rfl⟩
      intro j
      positivity
    · simpa [finitely_generated_cone] using
        cone_convex (R := ℝ) (Set.range fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ))
  · intro u hu
    rcases (mem_finitely_generated_cone_iff).1 hu with ⟨μ, hμ_nonneg, hrepr⟩
    have hintPart :
        (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) ∈
          integral_intcone r := by
      exact (mem_integral_intcone_iff).2 ⟨fun j ↦ ⌊μ j⌋₊, rfl⟩
    have hfracPart :
        (∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ))) ∈
          convexHull ℝ (integral_intcone r) := by
      -- The fractional parts lie in `[0,1]`, so they form a convex combination of generators.
      exact fractional_combination_mem_convexHull_integral_intcone
        r
        (fun j ↦ Int.fract (μ j))
        (fun j ↦ Int.fract_nonneg (μ j))
        (fun j ↦ (Int.fract_lt_one (μ j)).le)
    have hsplit :
        u =
          (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) +
            ∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ)) := by
      -- Split each coefficient into its integer floor part plus its fractional remainder.
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
    rw [hsplit]
    simpa [add_comm] using add_mem_convexHull_integral_intcone hfracPart hintPart

/-- Helper for Theorem 1.5: the convex hull of a finite union of rational polytopes is again a
rational polytope. -/
lemma convexHull_iUnion_isRationalPolytope
    {d k : ℕ}
    (Q : Fin k → Set (Fin d → ℝ))
    (hQ : ∀ i, IsRationalPolytope (Q i)) :
    IsRationalPolytope (convexHull ℝ (⋃ i : Fin k, Q i)) := by
  classical
  choose m vertex hvertex using hQ
  let e :
      Fin (Fintype.card (Sigma fun i : Fin k ↦ Fin (m i))) ≃
        Sigma fun i : Fin k ↦ Fin (m i) :=
    (Fintype.equivFin (Sigma fun i : Fin k ↦ Fin (m i))).symm
  have hvertex_subset :
      Set.range (fun a : Sigma fun i : Fin k ↦ Fin (m i) ↦
          fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) ⊆
        ⋃ i : Fin k, Q i := by
    -- Every chosen rational vertex lies in the corresponding polytope, hence in the union.
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
          (Set.range fun a : Sigma fun i : Fin k ↦ Fin (m i) ↦
            fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) := by
    -- Each point of the union lies in one piece and then in the hull of the combined vertex set.
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
    rw [hvertex i] at hxi
    refine (convexHull_mono ?_) hxi
    rintro y ⟨j, rfl⟩
    exact ⟨⟨i, j⟩, rfl⟩
  have hEqSigma :
      convexHull ℝ (⋃ i : Fin k, Q i) =
        convexHull ℝ
          (Set.range fun a : Sigma fun i : Fin k ↦ Fin (m i) ↦
            fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) := by
    -- The two convex hulls coincide because each generating set is contained in the hull of the other.
    apply Set.Subset.antisymm
    · exact convexHull_min hiUnion_subset (convex_convexHull ℝ _)
    · refine convexHull_min ?_ (convex_convexHull ℝ _)
      intro x hx
      exact subset_convexHull ℝ _ (hvertex_subset hx)
  have hRange :
      Set.range (fun a : Sigma fun i : Fin k ↦ Fin (m i) ↦
          fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) =
        Set.range (fun i : Fin (Fintype.card (Sigma fun i : Fin k ↦ Fin (m i))) ↦
          fun j : Fin d ↦ (vertex (e i).1 (e i).2 j : ℝ)) := by
    -- Reindex the sigma-indexed finite vertex family by `Fin`.
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨e.symm a, ?_⟩
      ext j
      simpa using congrArg (fun b : Sigma fun i : Fin k ↦ Fin (m i) ↦ vertex b.1 b.2 j)
        (e.apply_symm_apply a)
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
  refine ⟨Fintype.card (Sigma fun i : Fin k ↦ Fin (m i)),
    fun i j ↦ vertex (e i).1 (e i).2 j, ?_⟩
  rw [hEqSigma, hRange]

/-- Helper for Theorem 1.5: every local rational polytope is an ordinary polytope in the Chapter 3
owner. -/
theorem IsRationalPolytope.isPolytope
    {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsRationalPolytope P) :
    P.IsPolytope ℝ := by
  rcases hP with ⟨k, v, rfl⟩
  exact ⟨Set.range (fun i : Fin k ↦ fun j : Fin d ↦ (v i j : ℝ)), Set.finite_range _, rfl⟩

/-- Helper for Theorem 1.5: the visible `x`-block projection of mixed-integer points in
`ℤ^q × ℝ^(n+p)`. -/
private def mixed_integer_x_projection
    {n p q : ℕ} (P : Set (MixedRealPoint q (n + p))) : Set (Fin n → ℝ) :=
  (fun wz : MixedRealPoint q (n + p) ↦ fun i ↦ wz.2 (Fin.castAdd p i)) '' mixed_integer_points P

/-- Helper for Theorem 1.5: membership in the visible `x`-projection is exactly the existence of
auxiliary real and integer blocks extending `x` to a mixed-integer point of `P`. -/
private theorem mem_mixed_integer_x_projection_iff
    {n p q : ℕ}
    {P : Set (MixedRealPoint q (n + p))}
    {x : Fin n → ℝ} :
    x ∈ mixed_integer_x_projection P ↔
      ∃ y : Fin p → ℝ, ∃ z : Fin q → ℤ,
        ((fun j ↦ (z j : ℝ)), Fin.append x y) ∈ P := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    -- Unpack the mixed-integer witness and read off its visible and auxiliary coordinates.
    rcases (mem_mixed_integer_points_iff).1 hw with ⟨hP, hwMixed⟩
    have hwInt : w.1 ∈ integerVectors q := by
      simpa using (mem_mixed_integer_lattice_iff (n := q) (p := n + p) (xy := w)).1 hwMixed
    rcases (mem_integerVectors_iff (n := q) (x := w.1)).1 hwInt with ⟨z, hz⟩
    refine ⟨fun j ↦ w.2 (Fin.natAdd n j), z, ?_⟩
    have hw₂ :
        Fin.append (fun i ↦ w.2 (Fin.castAdd p i)) (fun j ↦ w.2 (Fin.natAdd n j)) = w.2 := by
      funext j
      refine Fin.addCases ?_ ?_ j
      · intro i
        simp
      · intro i
        simp
    have hpair :
        ((fun j ↦ (z j : ℝ)),
            Fin.append (fun i ↦ w.2 (Fin.castAdd p i)) (fun j ↦ w.2 (Fin.natAdd n j))) = w := by
      apply Prod.ext
      · funext j
        exact congrFun hz.symm j
      · exact hw₂
    simpa [hpair] using hP
  · rintro ⟨y, z, hP⟩
    -- Repackage the supplied extension as a mixed-integer witness of the projection.
    refine ⟨((fun j ↦ (z j : ℝ)), Fin.append x y), ?_, ?_⟩
    · refine (mem_mixed_integer_points_iff).2 ⟨hP, ?_⟩
      rw [mem_mixed_integer_lattice_iff]
      exact (mem_integerVectors_iff (n := q) (x := fun j ↦ (z j : ℝ))).2 ⟨z, rfl⟩
    · funext i
      simp

/-- Helper for Theorem 1.5: the unit box is the convex hull of its `0/1` vertices, hence a
rational polytope. -/
private lemma unitBox_isRationalPolytope
    (d : ℕ) :
    IsRationalPolytope (Set.univ.pi (fun _ : Fin d ↦ Set.Icc (0 : ℝ) 1)) := by
  let e : Fin (Fintype.card (Fin d → Bool)) ≃ (Fin d → Bool) :=
    (Fintype.equivFin (Fin d → Bool)).symm
  let v : Fin (Fintype.card (Fin d → Bool)) → Fin d → ℚ := fun i j ↦ if e i j then 1 else 0
  have hRange :
      Set.range (fun i : Fin (Fintype.card (Fin d → Bool)) ↦ fun j : Fin d ↦ ((v i j : ℚ) : ℝ)) =
        zero_one_cube d := by
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
      let b : Fin d → Bool := fun j ↦ x j = 1
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
  have hCompact : IsCompact (Set.univ.pi (fun _ : Fin d ↦ Set.Icc (0 : ℝ) 1)) := by
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hConvex : Convex ℝ (Set.univ.pi (fun _ : Fin d ↦ Set.Icc (0 : ℝ) 1)) := by
    exact convex_pi fun _ _ ↦ convex_Icc (0 : ℝ) 1
  have hExtremeFinite :
      ((Set.univ.pi (fun _ : Fin d ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ).Finite := by
    rw [extremePoints_unit_box_eq_zero_one_cube, ← hRange]
    exact Set.finite_range _
  refine ⟨Fintype.card (Fin d → Bool), v, ?_⟩
  calc
    Set.univ.pi (fun _ : Fin d ↦ Set.Icc (0 : ℝ) 1)
        = closure (convexHull ℝ ((Set.univ.pi (fun _ : Fin d ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ)) := by
            simpa using (closure_convexHull_extremePoints hCompact hConvex).symm
    _ = convexHull ℝ ((Set.univ.pi (fun _ : Fin d ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ) := by
          rw [(hExtremeFinite.isClosed_convexHull ℝ).closure_eq]
    _ = convexHull ℝ (zero_one_cube d) := by
          rw [extremePoints_unit_box_eq_zero_one_cube]
    _ = convexHull ℝ
          (Set.range (fun i : Fin (Fintype.card (Fin d → Bool)) ↦ fun j : Fin d ↦ ((v i j : ℚ) : ℝ))) := by
            rw [← hRange]

/-- Helper for Theorem 1.5: applying a rational linear map to a rational polytope preserves a
rational vertex presentation. -/
private lemma isRationalPolytope_image_rationalMatrixMulVec
    {m d : ℕ}
    {P : Set (Fin m → ℝ)}
    (hP : IsRationalPolytope P)
    (A : Matrix (Fin d) (Fin m) ℚ) :
    IsRationalPolytope ((fun x : Fin m → ℝ ↦ (A.map (Rat.castHom ℝ)) *ᵥ x) '' P) := by
  rcases hP with ⟨k, v, hv⟩
  let w : Fin k → Fin d → ℚ := fun i ↦ A *ᵥ v i
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

/-- Helper for Theorem 1.5: Minkowski sums of rational polytopes stay rational. -/
private lemma isRationalPolytope_add
    {d : ℕ}
    {P Q : Set (Fin d → ℝ)}
    (hP : IsRationalPolytope P)
    (hQ : IsRationalPolytope Q) :
    IsRationalPolytope (P + Q) := by
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
        ⟨fun i : Fin d ↦ (v (e a).1 i : ℝ), ⟨(e a).1, rfl⟩,
          fun i : Fin d ↦ (w (e a).2 i : ℝ), ⟨(e a).2, rfl⟩, by
            ext s
            simp [e]⟩

/-- Helper for Theorem 1.5: every rational polytope in `ℝ^d` admits a rational matrix
presentation. -/
private lemma rationalPolytope_eq_rationalMatrixPolyhedron
    {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsRationalPolytope P) :
    ∃ m : ℕ,
      ∃ A : Matrix (Fin m) (Fin d) ℚ,
        ∃ b : Fin m → ℚ,
          P = rational_matrix_polyhedron A b := by
  rcases hP with ⟨k, v, rfl⟩
  let verticesReal : Fin k → Fin d → ℝ := fun i j ↦ (v i j : ℝ)
  let rays0 : Fin 0 → Fin d → ℚ := Fin.elim0
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
      v rays0 L hVertices (by intro j; exact Fin.elim0 j) with
    ⟨_π, m, A, b, hrepr, _, _⟩
  refine ⟨m, A, b, ?_⟩
  have hConeEmpty :
      cone (Set.range fun i : Fin 0 ↦ fun j : Fin d ↦ (rays0 i j : ℝ)) =
        ({0} : Set (Fin d → ℝ)) := by
    -- The empty ray family generates only the zero vector.
    simpa using (cone_empty : cone (∅ : Set (Fin d → ℝ)) = ({0} : Set (Fin d → ℝ)))
  have hAddZero :
      convexHull ℝ (Set.range verticesReal) + ({0} : Set (Fin d → ℝ)) =
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
        = convexHull ℝ (Set.range verticesReal) + ({0} : Set (Fin d → ℝ)) := by
            symm
            exact hAddZero
    _ = convexHull ℝ (Set.range verticesReal) +
          cone (Set.range fun i : Fin 0 ↦ fun j : Fin d ↦ (rays0 i j : ℝ)) := by
            rw [hConeEmpty]
    _ = rational_matrix_polyhedron A b := hrepr

/-- Helper for Theorem 1.5: after flattening `ℤ^q × ℝ^(n+p)` into `ℝ^(q+n+p)`, the visible
`x`-projection drops the leading integer block and the trailing auxiliary real block. -/
private def flattenedVisibleXProjection
    {n p q : ℕ} (u : Fin (q + (n + p)) → ℝ) : Fin n → ℝ :=
  fun l ↦ u (Fin.natAdd q (Fin.castAdd p l))

/-- Helper for Theorem 1.5: the flattened visible-`x` projection is linear. -/
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

/-- Helper for Theorem 1.5: projecting a flattened rational polytope to the visible `x` block
preserves rational polyhedrality. -/
private lemma isRationalPolytope_image_flattenedVisibleXProjection
    {n p q : ℕ}
    {Q : Set (Fin (q + (n + p)) → ℝ)}
    (hQ : IsRationalPolytope Q) :
    IsRationalPolytope (flattenedVisibleXProjection '' Q) := by
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

/-- Helper for Theorem 1.5: the canonical `x`-projection is exactly the image of the flattened
mixed-integer points under `flattenedVisibleXProjection`. -/
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

/-- Helper for Theorem 1.5: projecting a flattened finite union plus one integral cone to the
visible `x` block preserves the finite union and projects each integral ray. -/
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

/-- Helper for Theorem 1.5: once the mixed-integer points are decomposed on the flattened ambient
space, one visible-`x` projection yields the desired union of rational pieces plus the projected
integral cone. -/
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
  -- Compare the canonical `x`-projection to the same flattened witness surface, then project
  -- the finite union and cone in one step.
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

/-- Helper for Theorem 1.5: if one witness `mixed_integer_x_projection` has a flattened
union-plus-integral-cone decomposition, then the user-facing projection inherits the same shape
after visible-coordinate transport. -/
private lemma unionRationalPolytopesAddIntegralIntcone_ofRepresentableWitness
    {n p q : ℕ}
    {P : Set (MixedRealPoint q (n + p))}
    {S : Set (Fin n → ℝ)}
    (hSP : S = mixed_integer_x_projection P)
    (hflat :
      ∃ k t : ℕ,
        ∃ Q : Fin k → Set (Fin (q + (n + p)) → ℝ),
          ∃ r : Fin t → Fin (q + (n + p)) → ℤ,
            (∀ i : Fin k, IsRationalPolytope (Q i)) ∧
              Fin.appendEquiv q (n + p) '' mixed_integer_points P =
                (⋃ i : Fin k, Q i) + integral_intcone r) :
    ∃ k t : ℕ,
      ∃ P' : Fin k → Set (Fin n → ℝ),
        ∃ r' : Fin t → Fin n → ℤ,
          (∀ i : Fin k, IsRationalPolytope (P' i)) ∧
            S = (⋃ i : Fin k, P' i) + integral_intcone r' := by
  rcases hflat with ⟨k, t, Q, r, hQ, hdecomp⟩
  refine ⟨k, t, fun i ↦ flattenedVisibleXProjection '' Q i,
    fun j l ↦ r j (Fin.natAdd q (Fin.castAdd p l)), ?_, ?_⟩
  · intro i
    -- Each projected flat piece stays rational polyhedral under the visible-coordinate map.
    exact isRationalPolytope_image_flattenedVisibleXProjection (hQ i)
  · -- Rewrite the transported witness decomposition back to the user-facing set `S`.
    simpa [hSP] using xProjection_transport_ofFlattenedDecomposition (P := P) (Q := Q) (r := r) hdecomp

/-- Helper for Theorem 1.5: flattening rewrites mixed-integer membership as ambient flattened
membership together with integrality of the first block. -/
private lemma memFlatMixedIntegerPoints_iff
    {n p : ℕ}
    {P : Set (MixedRealPoint n p)}
    {u : Fin (n + p) → ℝ} :
    u ∈ (Fin.appendEquiv n p '' mixed_integer_points P) ↔
      u ∈ (Fin.appendEquiv n p '' P) ∧
        (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    -- Unpack flattened mixed-integer membership into ambient membership and first-block
    -- integrality.
    rcases (mem_mixed_integer_points_iff).1 hxy with ⟨hP, hxyLattice⟩
    constructor
    · exact ⟨xy, hP, rfl⟩
    · rw [mem_mixed_integer_lattice_iff] at hxyLattice
      simpa using hxyLattice
  · rintro ⟨huP, huInt⟩
    rcases huP with ⟨xy, hxyP, rfl⟩
    -- The flattened integrality condition is exactly the mixed-lattice condition on `xy`.
    refine ⟨xy, ?_, rfl⟩
    refine (mem_mixed_integer_points_iff).2 ⟨hxyP, ?_⟩
    rw [mem_mixed_integer_lattice_iff]
    simpa using huInt

/-- Helper for Theorem 1.5: the flattened points whose first `n` coordinates are integral. -/
private def firstBlockIntegerSet
    {n p : ℕ} : Set (Fin (n + p) → ℝ) :=
  {u | (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n}

/-- Helper for Theorem 1.5: the sum of two integer vectors is again an integer vector. -/
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

/-- Helper for Theorem 1.5: subtracting one integer vector from another stays in the integer
lattice. -/
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

/-- Helper for Theorem 1.5: every element of `integral_intcone r` has integral first block. -/
private lemma firstBlock_mem_integerVectors_of_mem_integralIntcone
    {n p q : ℕ}
    {r : Fin q → Fin (n + p) → ℤ}
    {u : Fin (n + p) → ℝ}
    (hu : u ∈ integral_intcone r) :
    (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
  rcases (mem_integral_intcone_iff).1 hu with ⟨a, rfl⟩
  -- The first block is a finite integer linear combination of integral ray coordinates.
  refine (mem_integerVectors_iff).2 ⟨fun i ↦ ∑ j : Fin q, (a j : ℤ) * r j (Fin.castAdd p i), ?_⟩
  funext i
  simp [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 1.5: once the flattened ambient set is normalized as
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

/-- Helper for Theorem 1.5: a rational polytope has a uniform integer bound on its first block. -/
private lemma boundedFirstBlockCoordinates_of_isRationalPolytope
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : IsRationalPolytope Q) :
    ∃ B : ℤ,
      ∀ ⦃u : Fin (n + p) → ℝ⦄, u ∈ Q → ∀ i : Fin n,
        (-(B : ℝ)) ≤ u (Fin.castAdd p i) ∧ u (Fin.castAdd p i) ≤ (B : ℝ) := by
  rcases (hQ.isPolytope) with ⟨V, hVfinite, hVeq⟩
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
    -- Coordinate norms are controlled by the ambient norm, which is controlled by the ball
    -- radius.
    calc
      |u (Fin.castAdd p i)| = ‖u (Fin.castAdd p i)‖ := by simp
      _ ≤ ‖u‖ := hcoord_norm
      _ ≤ R := hu_norm
      _ ≤ max R 0 := le_max_left _ _
  have hB_ge : max R 0 ≤ (B : ℝ) := Int.le_ceil (max R 0)
  exact abs_le.mp (hcoord_abs.trans hB_ge)

/-- Helper for Theorem 1.5: fixing the first `n` coordinates to one integer vector defines the
corresponding coordinate fiber. -/
private def firstBlockFiber
    {n p : ℕ}
    (z : Fin n → ℤ) : Set (Fin (n + p) → ℝ) :=
  {u | (fun i : Fin n ↦ u (Fin.castAdd p i)) = Int.cast ∘ z}

/-- Helper for Theorem 1.5: a bounded nonempty set has no nonzero recession direction. -/
private lemma recessionCone_eq_singleton_zero_of_nonempty_bounded
    {d : ℕ}
    {P : Set (Fin d → ℝ)}
    (hP_nonempty : P.Nonempty)
    (hP_bounded : Bornology.IsBounded P) :
    recessionCone P = ({0} : Set (Fin d → ℝ)) := by
  obtain ⟨x₀, hx₀⟩ := hP_nonempty
  have htranslate : ({x₀} + recessionCone P) ⊆ P := by
    -- Translate any recession direction by one feasible base point to stay inside `P`.
    rintro y ⟨x', hx', r, hr, rfl⟩
    rw [Set.mem_singleton_iff] at hx'
    subst x'
    rw [mem_recessionCone_iff] at hr
    simpa using hr hx₀ 1 zero_le_one
  have hrec_bounded : Bornology.IsBounded (recessionCone P) := by
    -- The translated recession cone sits inside the bounded ambient set `P`.
    obtain ⟨R, _, hP_ball⟩ := hP_bounded.subset_ball_lt 0 (0 : Fin d → ℝ)
    exact Bornology.IsBounded.subset
      (show Bornology.IsBounded (Metric.ball (0 : Fin d → ℝ) (R + ‖x₀‖)) from
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
    · obtain ⟨R, hR⟩ := hrec_bounded.subset_closedBall (0 : Fin d → ℝ)
      have hzero_mem : (0 : Fin d → ℝ) ∈ recessionCone P := zero_mem_recessionCone
      have hR_nonneg : 0 ≤ R := by
        have hzero_ball : (0 : Fin d → ℝ) ∈ Metric.closedBall (0 : Fin d → ℝ) R := hR hzero_mem
        simpa [Metric.mem_closedBall] using hzero_ball
      have hr_norm_pos : 0 < ‖r‖ := norm_pos_iff.mpr hr0
      have hr_norm_ne : ‖r‖ ≠ 0 := ne_of_gt hr_norm_pos
      have ht_nonneg : 0 ≤ R / ‖r‖ + 1 := by positivity
      have htr_mem : ((R / ‖r‖ + 1) • r) ∈ recessionCone P :=
        smul_mem_recessionCone hr ht_nonneg
      have hmem_ball :
          ((R / ‖r‖ + 1) • r) ∈ Metric.closedBall (0 : Fin d → ℝ) R := hR htr_mem
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

/-- Helper for Theorem 1.5: a nonempty bounded rational matrix polyhedron is a rational
polytope. -/
private lemma rationalMatrixPolyhedron_isRationalPolytope_of_nonempty_bounded
    {m d : ℕ}
    {A : Matrix (Fin m) (Fin d) ℚ}
    {b : Fin m → ℚ}
    (hP_nonempty : (rational_matrix_polyhedron A b).Nonempty)
    (hP_bounded : Bornology.IsBounded (rational_matrix_polyhedron A b)) :
    IsRationalPolytope (rational_matrix_polyhedron A b) := by
  let P : Set (Fin d → ℝ) := rational_matrix_polyhedron A b
  have hP_rational : is_rational_polyhedron P := by
    -- The given rational matrix presentation is already a rational polyhedron description.
    exact ⟨m, A, b, rfl⟩
  have hP_rec_zero : recessionCone P = ({0} : Set (Fin d → ℝ)) :=
    recessionCone_eq_singleton_zero_of_nonempty_bounded hP_nonempty hP_bounded
  let emptyIntegralRays : Fin 0 → Fin d → ℤ := fun j ↦ Fin.elim0 j
  have hrec_empty :
      recessionCone P =
        finitely_generated_cone (fun j : Fin 0 ↦ fun i : Fin d ↦ (emptyIntegralRays j i : ℝ)) := by
    -- Boundedness collapses the recession cone to the empty ray family.
    calc
      recessionCone P = ({0} : Set (Fin d → ℝ)) := hP_rec_zero
      _ = cone (Set.range (fun j : Fin 0 ↦ fun i : Fin d ↦ (emptyIntegralRays j i : ℝ))) := by
            simpa using (cone_empty : cone (∅ : Set (Fin d → ℝ)) = ({0} : Set (Fin d → ℝ))).symm
      _ = finitely_generated_cone (fun j : Fin 0 ↦ fun i : Fin d ↦ (emptyIntegralRays j i : ℝ)) := by
            rfl
  rcases existsFlattenedRationalVertexPresentationCompatibleWithIntegralRays
      hP_rational hP_nonempty emptyIntegralRays hrec_empty with
    ⟨t, vQ, hrepr⟩
  refine ⟨t, vQ, ?_⟩
  have hConeEmpty :
      finitely_generated_cone (fun j : Fin 0 ↦ fun i : Fin d ↦ (emptyIntegralRays j i : ℝ)) =
        ({0} : Set (Fin d → ℝ)) := by
    -- The empty ray family generates only the zero vector.
    simpa [finitely_generated_cone, emptyIntegralRays] using
      (cone_empty : cone (∅ : Set (Fin d → ℝ)) = ({0} : Set (Fin d → ℝ)))
  calc
    P = convexHull ℝ (Set.range (fun i : Fin t ↦ fun u : Fin d ↦ (vQ i u : ℝ))) +
          finitely_generated_cone (fun j : Fin 0 ↦ fun i : Fin d ↦ (emptyIntegralRays j i : ℝ)) := hrepr
    _ = convexHull ℝ (Set.range (fun i : Fin t ↦ fun u : Fin d ↦ (vQ i u : ℝ))) +
          ({0} : Set (Fin d → ℝ)) := by
            rw [hConeEmpty]
    _ = convexHull ℝ (Set.range (fun i : Fin t ↦ fun u : Fin d ↦ (vQ i u : ℝ))) := by
          ext x
          constructor
          · intro hx
            rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, hsum⟩
            have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
            have hyx : y = x := by simpa [hz0] using hsum
            simpa [hyx] using hy
          · intro hx
            exact Set.mem_add.mpr ⟨x, hx, 0, Set.mem_singleton 0, by simp⟩

/-- Helper for Theorem 1.5: a singleton-weighted finite sum collapses to its active coordinate. -/
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

/-- Helper for Theorem 1.5: a selector row supported on the first block recovers the chosen
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
  -- Split the flattened coordinates into the first block and the tail block before collapsing the
  -- singleton selector.
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, zero_mul, Finset.sum_const_zero, add_zero]
  simpa using sumCastIteMul_eq_active (fun l : Fin n ↦ u (Fin.castAdd p l)) i c

/-- Helper for Theorem 1.5: augmenting a rational matrix presentation by paired `±Id` rows on the
first block cuts out the fixed-first-block fiber. -/
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

/-- Helper for Theorem 1.5: augmenting a rational matrix presentation by paired `±Id` rows on the
first block cuts out the fixed-first-block fiber. -/
private lemma firstBlockFiber_eq_rationalMatrixPolyhedron
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : IsRationalPolytope Q)
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

/-- Helper for Theorem 1.5: every fixed-first-block fiber of a rational polytope is again a
rational polytope. -/
private lemma firstBlockFiber_isRationalPolytope
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : IsRationalPolytope Q)
    (z : Fin n → ℤ) :
    IsRationalPolytope (Q ∩ firstBlockFiber z) := by
  classical
  by_cases hFiber_nonempty : (Q ∩ firstBlockFiber z).Nonempty
  · rcases firstBlockFiber_eq_rationalMatrixPolyhedron hQ z with ⟨m, A, b, hFiber_eq⟩
    have hQ_bounded : Bornology.IsBounded Q := by
      -- Rational polytopes are bounded because they are finite convex hulls.
      rcases (hQ.isPolytope) with ⟨V, hV, hVeq⟩
      simpa [hVeq] using (isBounded_convexHull).2 hV.isBounded
    have hFiber_bounded : Bornology.IsBounded (Q ∩ firstBlockFiber z) := by
      exact hQ_bounded.subset (by
        intro u hu
        exact hu.1)
    -- For a fixed first-block fiber, boundedness already kills the recession cone.
    have hFiber_nonempty_matrix : (rational_matrix_polyhedron A b).Nonempty := by
      rw [← hFiber_eq]
      exact hFiber_nonempty
    have hFiber_bounded_matrix : Bornology.IsBounded (rational_matrix_polyhedron A b) := by
      rw [← hFiber_eq]
      exact hFiber_bounded
    simpa [hFiber_eq] using
      rationalMatrixPolyhedron_isRationalPolytope_of_nonempty_bounded
        hFiber_nonempty_matrix hFiber_bounded_matrix
  · have hFiber_empty : Q ∩ firstBlockFiber z = ∅ := Set.not_nonempty_iff_eq_empty.mp hFiber_nonempty
    -- The empty fiber is the convex hull of the empty rational vertex family.
    refine ⟨0, Fin.elim0, ?_⟩
    simpa [hFiber_empty]

/-- Helper for Theorem 1.5: the integer slice of one rational polytope is a finite union of
fixed-first-block rational-polytopal fibers. -/
private lemma existsRationalPolytopeFirstBlockIntegerSlices
    {n p : ℕ}
    {Q : Set (Fin (n + p) → ℝ)}
    (hQ : IsRationalPolytope Q) :
    ∃ K : ℕ,
      ∃ Qs : Fin K → Set (Fin (n + p) → ℝ),
        (∀ j : Fin K, IsRationalPolytope (Qs j)) ∧
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
  · -- Enumerate bounded integer first blocks of one piece and then recover the full slice.
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

/-- Helper for Theorem 1.5: the auxiliary integer-variable matrix adds `±Id` rows for the first
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

/-- Helper for Theorem 1.5: the auxiliary real-variable matrix keeps the original flattened
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

/-- Helper for Theorem 1.5: the lifted witness system reuses the original right-hand side and uses
zero on the equality rows. -/
private def flatMixedIntegerWitnessRhs
    {n m : ℕ}
    (b : Fin m → ℚ) :
    Fin (m + (n + n)) → ℚ :=
  Fin.addCases b (Fin.addCases (fun _ ↦ 0) (fun _ ↦ 0))

/-- Helper for Theorem 1.5: the first equality-row block of the integer witness matrix picks out
the chosen integer coordinate. -/
private lemma flatMixedIntegerWitnessIntFirstRow
    {n m : ℕ}
    (z : Fin n → ℤ)
    (i : Fin n) :
    (((flatMixedIntegerWitnessIntMatrix).map (Rat.castHom ℝ)) *ᵥ
        fun j ↦ (z j : ℝ)) (Fin.natAdd m (Fin.castAdd n i)) =
      (z i : ℝ) := by
  -- Evaluate the `+Id` row by isolating the unique nonzero coefficient at `i`.
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [flatMixedIntegerWitnessIntMatrix, Fin.addCases_right]
  · intro j _ hj
    simp [flatMixedIntegerWitnessIntMatrix, Fin.addCases_right, hj]
  · simp [flatMixedIntegerWitnessIntMatrix, Fin.addCases_right]

/-- Helper for Theorem 1.5: the second equality-row block of the integer witness matrix contributes
the negated chosen integer coordinate. -/
private lemma flatMixedIntegerWitnessIntSecondRow
    {n m : ℕ}
    (z : Fin n → ℤ)
    (i : Fin n) :
    (((flatMixedIntegerWitnessIntMatrix).map (Rat.castHom ℝ)) *ᵥ
        fun j ↦ (z j : ℝ)) (Fin.natAdd m (Fin.natAdd n i)) =
      -(z i : ℝ) := by
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

/-- Helper for Theorem 1.5: the first equality-row block of the real witness matrix records the
negated first-block coordinate of the ambient point. -/
private lemma flatMixedIntegerWitnessRealFirstRow
    {n p m : ℕ}
    (A : Matrix (Fin m) (Fin (n + p)) ℚ)
    (u : Fin (n + p) → ℝ)
    (i : Fin n) :
    (((flatMixedIntegerWitnessRealMatrix A).map (Rat.castHom ℝ)) *ᵥ
        u) (Fin.natAdd m (Fin.castAdd n i)) =
      -u (Fin.castAdd p i) := by
  -- Split the flattened coordinates into the first `n` block and the trailing `p` block.
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Finset.sum_eq_single i]
  · simp [flatMixedIntegerWitnessRealMatrix, Fin.addCases_right]
  · intro j _ hj
    simp [flatMixedIntegerWitnessRealMatrix, Fin.addCases_right, hj]
  · simp [flatMixedIntegerWitnessRealMatrix, Fin.addCases_right]

/-- Helper for Theorem 1.5: the second equality-row block of the real witness matrix records the
first-block coordinate of the ambient point. -/
private lemma flatMixedIntegerWitnessRealSecondRow
    {n p m : ℕ}
    (A : Matrix (Fin m) (Fin (n + p)) ℚ)
    (u : Fin (n + p) → ℝ)
    (i : Fin n) :
    (((flatMixedIntegerWitnessRealMatrix A).map (Rat.castHom ℝ)) *ᵥ
        u) (Fin.natAdd m (Fin.natAdd n i)) =
      u (Fin.castAdd p i) := by
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

/-- Helper for Theorem 1.5: the second equality-row block of the lifted right-hand side is zero. -/
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

/-- Helper for Theorem 1.5: membership in the lifted witness polyhedron is exactly ambient
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
    · -- The leading rows are exactly the original ambient inequalities.
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
        have hi' : -(z i : ℝ) + u (Fin.castAdd p i) ≤ 0 := by exact hi
        have hi'' : u (Fin.castAdd p i) ≤ (z i : ℝ) := by linarith
        exact hi''
      · have hi := h (Fin.natAdd m (Fin.castAdd n i))
        have hIntRow := flatMixedIntegerWitnessIntFirstRow (m := m) z i
        have hRealRow := flatMixedIntegerWitnessRealFirstRow (m := m) A u i
        rw [Pi.add_apply, hIntRow, hRealRow] at hi
        have hi' : (z i : ℝ) + -u (Fin.castAdd p i) ≤ 0 := by
          simpa [flatMixedIntegerWitnessRhs] using hi
        have hi'' : (z i : ℝ) ≤ u (Fin.castAdd p i) := by linarith
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
        have hrow : (z j' : ℝ) + -u (Fin.castAdd p j') ≤ 0 := by simpa [hj']
        rw [Pi.add_apply, hIntRow, hRealRow]
        simpa [flatMixedIntegerWitnessRhs] using hrow
      · intro j'
        have hj' : u (Fin.castAdd p j') = (z j' : ℝ) := congrFun huz j'
        have hIntRow := flatMixedIntegerWitnessIntSecondRow (m := m) z j'
        have hRealRow := flatMixedIntegerWitnessRealSecondRow (m := m) A u j'
        have hrow : -(z j' : ℝ) + u (Fin.castAdd p j') ≤ 0 := by simpa [hj']
        rw [Pi.add_apply, hIntRow, hRealRow]
        have hRhs :
            (fun j ↦ (flatMixedIntegerWitnessRhs b j : ℝ))
                (Fin.natAdd m (Fin.natAdd n j')) = 0 := by
          simpa using flatMixedIntegerWitnessRhsSecondRow (n := n) b j'
        rw [hRhs]
        exact hrow

/-- Helper for Theorem 1.5: the flattened mixed-integer set is the `x`-projection of the explicit
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
      flatMixedIntegerWitnessRealMatrix A, flatMixedIntegerWitnessRhs b, rfl⟩
  · -- Identify the flattened mixed-integer set with the witness `x`-projection.
    ext u
    rw [mem_mixed_integer_x_projection_iff]
    constructor
    · intro hu
      rcases (memFlatMixedIntegerPoints_iff).1 hu with ⟨huP, huZ⟩
      rw [hPflat_eq] at huP
      rcases (mem_integerVectors_iff).1 huZ with ⟨z, hz⟩
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
      have hzW' := (memFlatMixedIntegerWitnessPolyhedron_iff).1 hzWitness
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

/-- Helper for Theorem 1.5: every rational vector has a positive common denominator. -/
private lemma rationalVectorCommonDenominator_ne_zero
    {d : ℕ}
    (v : Fin d → ℚ) :
    rational_vector_common_denominator v ≠ 0 := by
  have hden :
      ∀ i ∈ (Finset.univ : Finset (Fin d)), (v i).den ≠ 0 := by
    intro i hi
    exact Nat.ne_of_gt (Rat.den_pos (v i))
  simpa [rational_vector_common_denominator] using (Finset.lcm_ne_zero_iff.2 hden)

/-- Helper for Theorem 1.5: clearing denominators rescales a rational vector by its common
denominator. -/
private lemma commonDenominatorScaledVector_eq_smulReal
    {d : ℕ}
    (v : Fin d → ℚ) :
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

/-- Helper for Theorem 1.5: clearing denominators on every rational ray does not change the
generated cone. -/
private lemma commonDenominatorScaledRays_eq_finitelyGeneratedCone
    {d q : ℕ}
    (r : Fin q → Fin d → ℚ) :
    finitely_generated_cone
        (fun j : Fin q ↦ fun i : Fin d ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) =
      finitely_generated_cone (fun j : Fin q ↦ fun i : Fin d ↦ (r j i : ℝ)) := by
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
        x = ∑ j : Fin q, μ j • (fun i : Fin d ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) := hrepr
        _ = ∑ j : Fin q,
              (μ j * (rational_vector_common_denominator (r j) : ℝ)) •
                (fun i : Fin d ↦ (r j i : ℝ)) := by
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
      exact_mod_cast rationalVectorCommonDenominator_ne_zero (v := r j)
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j / (rational_vector_common_denominator (r j) : ℝ), ?_, ?_⟩
    · intro j
      exact div_nonneg (hμ_nonneg j) (hD_nonneg j)
    · calc
        x = ∑ j : Fin q, μ j • (fun i : Fin d ↦ (r j i : ℝ)) := hrepr
        _ = ∑ j : Fin q,
              (μ j / (rational_vector_common_denominator (r j) : ℝ)) •
                (fun i : Fin d ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [commonDenominatorScaledVector_eq_smulReal (v := r j), smul_smul,
                div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (hD_ne_zero j), mul_one]

/-- Helper for Theorem 1.5: a nonempty flattened rational mixed polyhedron admits finitely many
integral generators for its recession cone. -/
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
  -- denominators on each rational generator.
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

/-- Helper for Theorem 1.5: the coefficient unit box is a rational polytope. -/
private lemma coefficientUnitBox_isRationalPolytope
    (q : ℕ) :
    IsRationalPolytope (Set.univ.pi (fun _ : Fin q ↦ Set.Icc (0 : ℝ) 1)) :=
  unitBox_isRationalPolytope q

/-- Helper for Theorem 1.5: the fractional coefficient box for an integral ray family is the image
of the unit box under the corresponding rational linear map. -/
private def fractionalRayBox
    {d q : ℕ}
    (rays : Fin q → Fin d → ℤ) :
    Set (Fin d → ℝ) :=
  (fun μ : Fin q → ℝ ↦ ∑ j : Fin q, μ j • (fun i : Fin d ↦ (rays j i : ℝ))) ''
    Set.univ.pi (fun _ : Fin q ↦ Set.Icc (0 : ℝ) 1)

/-- Helper for Theorem 1.5: the fractional coefficient box of an integral ray family is a rational
polytope. -/
private lemma fractionalRayBox_isRationalPolytope
    {d q : ℕ}
    (rays : Fin q → Fin d → ℤ) :
    IsRationalPolytope (fractionalRayBox rays) := by
  let A : Matrix (Fin d) (Fin q) ℚ := fun i j ↦ (rays j i : ℚ)
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

/-- Helper for Theorem 1.5: the real cone generated by integral rays splits into a bounded
fractional part plus the integral cone. -/
private lemma finitelyGeneratedCone_eq_fractionalRayBox_add_integralIntcone
    {d q : ℕ}
    (rays : Fin q → Fin d → ℤ) :
    finitely_generated_cone (fun j : Fin q ↦ fun i : Fin d ↦ (rays j i : ℝ)) =
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
    refine ⟨∑ j : Fin q, frac j • (fun i : Fin d ↦ (rays j i : ℝ)), ?_,
      ∑ j : Fin q, (a j : ℝ) • (fun i : Fin d ↦ (rays j i : ℝ)), ?_, ?_⟩
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

/-- Helper for Theorem 1.5: once the recession rays are integral, the ambient flattened witness
can be normalized to one rational polytope plus one integral cone. -/
private lemma flatAmbient_eq_rationalPolytope_add_integralIntcone_of_nonempty
    {n p : ℕ}
    {W : Set (MixedRealPoint n p)}
    (hW : is_rational_mixed_polyhedron W)
    (hW_nonempty : Set.Nonempty W) :
    ∃ t : ℕ,
      ∃ Q0 : Set (Fin (n + p) → ℝ),
        ∃ r : Fin t → Fin (n + p) → ℤ,
          IsRationalPolytope Q0 ∧
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
  have hQbase : IsRationalPolytope Qbase := by
    exact ⟨s, vQ, rfl⟩
  refine ⟨t, Qbase + fractionalRayBox r, r, isRationalPolytope_add hQbase
    (fractionalRayBox_isRationalPolytope r), ?_⟩
  -- Absorb the bounded fractional coefficients into one extra rational polytope.
  calc
    Fin.appendEquiv n p '' W
        = Qbase + finitely_generated_cone (fun j : Fin t ↦ fun i : Fin (n + p) ↦ (r j i : ℝ)) := by
            simpa [Qbase] using hQbase_repr
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

/-- Helper for Theorem 1.5: in the nonempty case, the flattened mixed-integer set should admit
the finite-union-plus-integral-cone decomposition needed by the local Meyer hull proof. -/
theorem flatMixedIntegerPoints_eq_iUnion_rationalPolytopes_add_integralIntcone_of_nonempty
    {P : Set (MixedRealPoint n p)}
    (hP : is_rational_mixed_polyhedron P)
    (hS_nonempty : Set.Nonempty (mixed_integer_points P)) :
    ∃ k q : ℕ,
      ∃ Q : Fin k → Set (Fin (n + p) → ℝ),
        ∃ r : Fin q → Fin (n + p) → ℤ,
          (∀ i : Fin k, IsRationalPolytope (Q i)) ∧
            Fin.appendEquiv n p '' mixed_integer_points P =
              (⋃ i : Fin k, Q i) + integral_intcone r := by
  -- Route correction: normalize the flattened target through an explicit `mixed_integer_x_projection`
  -- witness, decompose that witness ambiently as `polytope + integral_intcone`, and then
  -- transport the resulting visible-coordinate decomposition back to the target flattened set.
  rcases exists_explicitFlatMixedIntegerProjectionWitness P hP with ⟨W, hW, hWproj⟩
  have hWflat :
      ∃ k q : ℕ,
        ∃ Q : Fin k → Set (Fin (n + (n + p)) → ℝ),
          ∃ r : Fin q → Fin (n + (n + p)) → ℤ,
            (∀ i : Fin k, IsRationalPolytope (Q i)) ∧
              Fin.appendEquiv n (n + p) '' mixed_integer_points W =
                (⋃ i : Fin k, Q i) + integral_intcone r := by
    have hW_nonempty : Set.Nonempty W := by
      -- One mixed-integer point of `P` yields one witness point of `W`.
      rcases hS_nonempty with ⟨w, hw⟩
      have hwproj :
          Fin.appendEquiv n p w ∈
            mixed_integer_x_projection (n := n + p) (p := 0) (q := n) W := by
        rw [← hWproj]
        exact ⟨w, hw, rfl⟩
      rcases (mem_mixed_integer_x_projection_iff).1 hwproj with ⟨y, z, hzW⟩
      have hy :
          Fin.append (Fin.appendEquiv n p w) y = Fin.appendEquiv n p w := by
        funext i
        simpa using Fin.append_left (Fin.appendEquiv n p w) y i
      refine ⟨((fun j ↦ (z j : ℝ)), Fin.appendEquiv n p w), ?_⟩
      simpa [hy] using hzW
    rcases flatAmbient_eq_rationalPolytope_add_integralIntcone_of_nonempty hW hW_nonempty with
      ⟨q, Qflat, r, hQflat, hWambient⟩
    have hWslice :
        Fin.appendEquiv n (n + p) '' mixed_integer_points W =
          (Qflat ∩ firstBlockIntegerSet) + integral_intcone r := by
      -- Rewrite the flattened mixed-integer witness through the ambient decomposition before
      -- replacing the bounded integer slice by finitely many rational-polytopal fibers.
      simpa using flatMixedIntegerPoints_eq_baseSlice_add_integralIntcone hWambient
    rcases existsRationalPolytopeFirstBlockIntegerSlices hQflat with
      ⟨K, Qslice, hQslice, hslice⟩
    refine ⟨K, q, Qslice, r, hQslice, ?_⟩
    calc
      Fin.appendEquiv n (n + p) '' mixed_integer_points W
          = (Qflat ∩ firstBlockIntegerSet) + integral_intcone r := hWslice
      _ = (⋃ j : Fin K, Qslice j) + integral_intcone r := by
            rw [hslice]
  -- Once the witness `W` is decomposed in flattened coordinates, the visible-coordinate
  -- transport package rewrites the witness decomposition back to the target set.
  exact
    unionRationalPolytopesAddIntegralIntcone_ofRepresentableWitness
      hWproj hWflat

/-- Helper for Theorem 1.5: a rational mixed polyhedron has a rational mixed-integer hull, proved
locally once the flattened nonempty Meyer decomposition is available. -/
theorem mixed_integer_hull_is_rational_mixed_polyhedron_local
    {P : Set (MixedRealPoint n p)}
    (hP : is_rational_mixed_polyhedron P) :
    is_rational_mixed_polyhedron (convexHull ℝ (mixed_integer_points P)) := by
  -- Work in the flattened ambient space `ℝ^(n+p)` to match the Chapter 3 hull API.
  change is_rational_polyhedron ((Fin.appendEquiv n p) '' convexHull ℝ (mixed_integer_points P))
  rw [appendEquiv_image_convexHull]
  by_cases hS_nonempty : Set.Nonempty (mixed_integer_points P)
  · rcases
      flatMixedIntegerPoints_eq_iUnion_rationalPolytopes_add_integralIntcone_of_nonempty
        (P := P) hP hS_nonempty with
      ⟨k, q, Q, r, hQ, hflat⟩
    have hU_rational :
        IsRationalPolytope (convexHull ℝ (⋃ i : Fin k, Q i)) :=
      convexHull_iUnion_isRationalPolytope Q hQ
    rcases hU_rational with ⟨t, vertices, hvertices⟩
    let raysQ : Fin q → Fin (n + p) → ℚ := fun j i ↦ (r j i : ℚ)
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
              (fun j ↦ EncodingSize.rationalVector (vertices j)) := by
        simpa using
          (Finset.le_sup
            (s := (Finset.univ : Finset (Fin t)))
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
              (fun t ↦ EncodingSize.rationalVector (raysQ t)) := by
        simpa using
          (Finset.le_sup
            (s := (Finset.univ : Finset (Fin q)))
            (f := fun t ↦ EncodingSize.rationalVector (raysQ t))
            (b := j)
            (by simp))
      exact le_trans hj (Nat.le_max_right _ _)
    rcases exists_rational_matrix_polyhedron_of_bounded_rational_vrepresentation_encoding
        vertices raysQ L hvertices_bound hrays_bound with
      ⟨_π, m, A, b, hrepr, _, _⟩
    refine ⟨m, A, b, ?_⟩
    calc
      convexHull ℝ (Fin.appendEquiv n p '' mixed_integer_points P)
          = convexHull ℝ ((⋃ i : Fin k, Q i) + integral_intcone r) := by
              rw [hflat]
      _ = convexHull ℝ (⋃ i : Fin k, Q i) + convexHull ℝ (integral_intcone r) := by
            rw [convexHull_add]
      _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin (n + p) ↦ (vertices i u : ℝ)) +
            convexHull ℝ (integral_intcone r) := by
              rw [hvertices]
      _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin (n + p) ↦ (vertices i u : ℝ)) +
            finitely_generated_cone
              (fun j : Fin q ↦ fun u : Fin (n + p) ↦ (r j u : ℝ)) := by
              rw [convexHull_integral_intcone_eq_finitely_generated_cone]
      _ = rational_matrix_polyhedron A b := by
            simpa [raysQ, finitely_generated_cone] using hrepr
  · have hS_empty : mixed_integer_points P = ∅ := Set.not_nonempty_iff_eq_empty.mp hS_nonempty
    -- In the empty case, the hull is empty and the explicit inconsistent inequality witness suffices.
    simpa [hS_empty] using (is_rational_polyhedron_empty (k := n + p))

end Theorem15Support

/-- Theorem 1.5. If
`S = nonnegative_rational_mixed_integer_points A G b`, then
`convexHull ℝ S` is a rational mixed polyhedron. -/
theorem nonnegative_rational_mixed_integer_hull_is_rational_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) :
    is_rational_mixed_polyhedron
      (convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)) := by
  -- Route correction: delegate the generic hull-normalization argument to the item-owned support
  -- file, then discharge the only remaining hypothesis with the already proved nonnegative owner.
  simpa using
    Theorem15Support.mixed_integer_hull_is_rational_mixed_polyhedron_local
      (P := nonnegative_rational_mixed_polyhedron A G b)
      (nonnegative_rational_mixed_polyhedron_is_rational_mixed_polyhedron A G b)

/-- The convex hull of the nonnegative rational mixed-integer feasible set admits a rational
mixed-system presentation. -/
theorem nonnegative_rational_mixed_integer_hull_has_rational_presentation
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) :
    ∃ m' : ℕ,
      ∃ A' : Matrix (Fin m') (Fin n) ℚ,
        ∃ G' : Matrix (Fin m') (Fin p) ℚ,
          ∃ b' : Fin m' → ℚ,
            convexHull ℝ (nonnegative_rational_mixed_integer_points A G b) =
              rational_mixed_polyhedron A' G' b' := by
  -- Once the hull is known to be a rational mixed polyhedron, this is just the owner expansion.
  exact (is_rational_mixed_polyhedron_iff).1
    (nonnegative_rational_mixed_integer_hull_is_rational_mixed_polyhedron A G b)

end Theorem15
