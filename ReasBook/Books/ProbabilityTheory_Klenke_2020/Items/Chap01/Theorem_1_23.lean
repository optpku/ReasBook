/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open Set MeasureTheory MeasurableSpace Metric TopologicalSpace

-- Declarations for this item will be appended below by the statement pipeline.

/-- The twelve canonical generator families `E₁, …, E₁₂` used to generate the Borel
`σ`-algebra of `ℝⁿ`. -/
inductive EuclideanBorelGenerator where
  /-- The class of open subsets of `ℝⁿ`. -/
  | openSets
  /-- The class of closed subsets of `ℝⁿ`. -/
  | closedSets
  /-- The class of compact subsets of `ℝⁿ`. -/
  | compactSets
  /-- The class of open balls with rational center and positive rational radius. -/
  | rationalOpenBalls
  /-- The class of open rectangles with rational endpoints. -/
  | rationalOpenRectangles
  /-- The class of closed rectangles with rational endpoints. -/
  | rationalClosedRectangles
  /-- The class of left-open right-closed rectangles with rational endpoints. -/
  | rationalLeftOpenRightClosedRectangles
  /-- The class of left-closed right-open rectangles with rational endpoints. -/
  | rationalLeftClosedRightOpenRectangles
  /-- The class of open lower orthants with rational upper endpoint. -/
  | rationalOpenLowerOrthants
  /-- The class of closed lower orthants with rational upper endpoint. -/
  | rationalClosedLowerOrthants
  /-- The class of open upper orthants with rational lower endpoint. -/
  | rationalOpenUpperOrthants
  /-- The class of closed upper orthants with rational lower endpoint. -/
  | rationalClosedUpperOrthants

namespace EuclideanBorelGenerator

/-- The rational generator families `E₄, \ldots, E₁₂`. -/
def IsRational : EuclideanBorelGenerator → Prop
  | .openSets => False
  | .closedSets => False
  | .compactSets => False
  | _ => True

end EuclideanBorelGenerator

/-- For a fixed dimension `n`, this returns the corresponding generator class `Eᵢ` of subsets
of the Euclidean space `ℝⁿ`, modeled as `Fin n → ℝ`. For `E₄`, the balls are the genuine
Euclidean balls on `EuclideanSpace ℝ (Fin n)`, transported along `EuclideanSpace.equiv`. -/
def euclideanBorelGeneratorClass (n : ℕ) :
    EuclideanBorelGenerator → Set (Set (Fin n → ℝ))
  | .openSets => {s | IsOpen s}
  | .closedSets => {s | IsClosed s}
  | .compactSets => {s | IsCompact s}
  | .rationalOpenBalls =>
      let e : EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) :=
        (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
      {s | ∃ c : Fin n → ℚ, ∃ r : ℚ, 0 < r ∧
        s = e '' Metric.ball (e.symm (fun j ↦ (c j : ℝ))) (r : ℝ)}
  | .rationalOpenRectangles =>
      {s | ∃ a b : Fin n → ℚ, (∀ j, a j < b j) ∧
        s = {x | ∀ j, (a j : ℝ) < x j ∧ x j < (b j : ℝ)}}
  | .rationalClosedRectangles =>
      {s | ∃ a b : Fin n → ℚ, (∀ j, a j ≤ b j) ∧
        s = {x | ∀ j, (a j : ℝ) ≤ x j ∧ x j ≤ (b j : ℝ)}}
  | .rationalLeftOpenRightClosedRectangles =>
      {s | ∃ a b : Fin n → ℚ, (∀ j, a j < b j) ∧
        s = {x | ∀ j, (a j : ℝ) < x j ∧ x j ≤ (b j : ℝ)}}
  | .rationalLeftClosedRightOpenRectangles =>
      {s | ∃ a b : Fin n → ℚ, (∀ j, a j < b j) ∧
        s = {x | ∀ j, (a j : ℝ) ≤ x j ∧ x j < (b j : ℝ)}}
  | .rationalOpenLowerOrthants =>
      {s | ∃ b : Fin n → ℚ, s = {x | ∀ j, x j < (b j : ℝ)}}
  | .rationalClosedLowerOrthants =>
      {s | ∃ b : Fin n → ℚ, s = {x | ∀ j, x j ≤ (b j : ℝ)}}
  | .rationalOpenUpperOrthants =>
      {s | ∃ a : Fin n → ℚ, s = {x | ∀ j, (a j : ℝ) < x j}}
  | .rationalClosedUpperOrthants =>
      {s | ∃ a : Fin n → ℚ, s = {x | ∀ j, (a j : ℝ) ≤ x j}}

/-- Helper for Theorem 1.23: a product family defined by one rational endpoint in each
coordinate is exactly the corresponding family of product boxes. -/
lemma rational_single_endpoint_generator_eq_pi (n : ℕ) (F : ℚ → Set ℝ) :
    {s : Set (Fin n → ℝ) | ∃ b : Fin n → ℚ, s = {x | ∀ j, x j ∈ F (b j)}} =
      Set.pi univ '' Set.pi univ
        (fun _ : Fin n => ⋃ q : ℚ, ({F q} : Set (Set ℝ))) := by
  classical
  -- Repackage the coordinatewise description as a genuine product of one-dimensional sets.
  ext s
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨fun j ↦ F (b j), ?_, ?_⟩
    · intro j _
      exact mem_iUnion.2 ⟨b j, by simp⟩
    · ext x
      simp
  · rintro ⟨t, ht, rfl⟩
    -- Extract the rational endpoint carried by each coordinate box.
    have hq : ∀ j : Fin n, ∃ q : ℚ, t j = F q := by
      intro j
      have : t j ∈ (⋃ q : ℚ, ({F q} : Set (Set ℝ))) := ht j (by simp)
      simpa [eq_comm] using this
    choose b hb using hq
    refine ⟨b, ?_⟩
    ext x
    simp [hb]

/-- Helper for Theorem 1.23: a product family defined by two rational endpoints in each
coordinate is exactly the corresponding family of product boxes. -/
lemma rational_two_endpoint_generator_eq_pi (n : ℕ) (F : ℚ → ℚ → Set ℝ) :
    {s : Set (Fin n → ℝ) |
        ∃ a b : Fin n → ℚ, (∀ j, a j < b j) ∧
          s = {x | ∀ j, x j ∈ F (a j) (b j)}} =
      Set.pi univ '' Set.pi univ
        (fun _ : Fin n =>
          ⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({F a b} : Set (Set ℝ))) := by
  classical
  -- Repackage the coordinatewise interval family as a genuine product of intervals.
  ext s
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨fun j ↦ F (a j) (b j), ?_, ?_⟩
    · intro j _
      exact mem_iUnion.2 ⟨a j, mem_iUnion.2 ⟨b j, mem_iUnion.2 ⟨hab j, by simp⟩⟩⟩
    · ext x
      simp
  · rintro ⟨t, ht, rfl⟩
    -- Extract the two rational endpoints carried by each coordinate interval.
    have hq : ∀ j : Fin n, ∃ a b : ℚ, a < b ∧ t j = F a b := by
      intro j
      have : t j ∈
          (⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({F a b} : Set (Set ℝ))) := ht j (by simp)
      simpa [eq_comm, exists_and_left, and_assoc] using this
    choose a b hab hb using hq
    refine ⟨a, b, hab, ?_⟩
    ext x
    simp [hb]

/-- Helper for Theorem 1.23: a product family defined by two rational endpoints in each
coordinate, allowing degenerate intervals, is exactly the corresponding family of product boxes. -/
lemma rational_two_endpoint_generator_eq_pi_le (n : ℕ) (F : ℚ → ℚ → Set ℝ) :
    {s : Set (Fin n → ℝ) |
        ∃ a b : Fin n → ℚ, (∀ j, a j ≤ b j) ∧
          s = {x | ∀ j, x j ∈ F (a j) (b j)}} =
      Set.pi univ '' Set.pi univ
        (fun _ : Fin n =>
          ⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a ≤ b), ({F a b} : Set (Set ℝ))) := by
  classical
  ext s
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨fun j ↦ F (a j) (b j), ?_, ?_⟩
    · intro j _
      exact mem_iUnion.2 ⟨a j, mem_iUnion.2 ⟨b j, mem_iUnion.2 ⟨hab j, by simp⟩⟩⟩
    · ext x
      simp
  · rintro ⟨t, ht, rfl⟩
    have hq : ∀ j : Fin n, ∃ a b : ℚ, a ≤ b ∧ t j = F a b := by
      intro j
      have : t j ∈
          (⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a ≤ b), ({F a b} : Set (Set ℝ))) := ht j (by simp)
      simpa [eq_comm, exists_and_left, and_assoc] using this
    choose a b hab hb using hq
    refine ⟨a, b, hab, ?_⟩
    ext x
    simp [hb]

/-- Helper for Theorem 1.23: once a one-dimensional rational box family generates the Borel
`σ`-algebra on `ℝ`, the corresponding product boxes generate the Borel `σ`-algebra on `ℝⁿ`. -/
lemma borel_eq_generateFrom_pi_boxes (n : ℕ) (C : Set (Set ℝ))
    (hC : borel ℝ = MeasurableSpace.generateFrom C)
    (hspan : IsCountablySpanning C) :
    borel (Fin n → ℝ) =
      MeasurableSpace.generateFrom (Set.pi univ '' Set.pi univ (fun _ : Fin n => C)) := by
  -- Identify the product measurable space with the Borel `σ`-algebra on the finite product.
  rw [← BorelSpace.measurable_eq (α := Fin n → ℝ)]
  symm
  exact generateFrom_eq_pi
    (fun _ ↦ hC.symm.trans (BorelSpace.measurable_eq (α := ℝ)).symm)
    (fun _ ↦ hspan)

/-- Helper for Theorem 1.23: rational rays of the form `(-∞, q)` span `ℝ` countably. -/
lemma rational_iio_isCountablySpanning :
    IsCountablySpanning (⋃ q : ℚ, ({Iio (q : ℝ)} : Set (Set ℝ))) := by
  -- The rays `(-∞, n)` already cover the line.
  refine ⟨fun n ↦ Iio (n : ℝ), ?_, ?_⟩
  · intro n
    exact mem_iUnion.2 ⟨n, by simp⟩
  · ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact mem_iUnion.2 ⟨n, by simpa using hn⟩

/-- Helper for Theorem 1.23: rational rays of the form `(-∞, q]` span `ℝ` countably. -/
lemma rational_iic_isCountablySpanning :
    IsCountablySpanning (⋃ q : ℚ, ({Iic (q : ℝ)} : Set (Set ℝ))) := by
  -- The rays `(-∞, n]` already cover the line.
  refine ⟨fun n ↦ Iic (n : ℝ), ?_, ?_⟩
  · intro n
    exact mem_iUnion.2 ⟨n, by simp⟩
  · ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact mem_iUnion.2 ⟨n, by simpa using hn.le⟩

/-- Helper for Theorem 1.23: rational rays of the form `(q, ∞)` span `ℝ` countably. -/
lemma rational_ioi_isCountablySpanning :
    IsCountablySpanning (⋃ q : ℚ, ({Ioi (q : ℝ)} : Set (Set ℝ))) := by
  -- The rays `(-n, ∞)` already cover the line.
  refine ⟨fun n ↦ Ioi (-(n + 1 : ℝ)), ?_, ?_⟩
  · intro n
    exact mem_iUnion.2 ⟨-(n + 1 : ℚ), by simp⟩
  · ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      have hmem : -(n : ℝ) < x := by
        have h' : -(n : ℝ) < x ∧ x < (n : ℝ) := by
          simpa [abs_lt] using hn
        exact h'.1
      exact mem_iUnion.2 ⟨n, by
        have hmem' : -((n + 1 : ℕ) : ℝ) < x := by
          have hlt : -((n + 1 : ℕ) : ℝ) < -(n : ℝ) := by
            norm_num
          exact hlt.trans hmem
        simpa [Nat.succ_eq_add_one] using hmem'⟩

/-- Helper for Theorem 1.23: rational rays of the form `[q, ∞)` span `ℝ` countably. -/
lemma rational_ici_isCountablySpanning :
    IsCountablySpanning (⋃ q : ℚ, ({Ici (q : ℝ)} : Set (Set ℝ))) := by
  -- The rays `[-n, ∞)` already cover the line.
  refine ⟨fun n ↦ Ici (-(n + 1 : ℝ)), ?_, ?_⟩
  · intro n
    exact mem_iUnion.2 ⟨-(n + 1 : ℚ), by simp⟩
  · ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      have hmem : -(n : ℝ) ≤ x := by
        have h' : -(n : ℝ) < x ∧ x < (n : ℝ) := by
          simpa [abs_lt] using hn
        exact h'.1.le
      exact mem_iUnion.2 ⟨n, by
        have hmem' : -((n + 1 : ℕ) : ℝ) ≤ x := by
          have hlt : -((n + 1 : ℕ) : ℝ) < -(n : ℝ) := by
            norm_num
          exact hlt.le.trans hmem
        simpa [Nat.succ_eq_add_one] using hmem'⟩

/-- Helper for Theorem 1.23: rational open intervals span `ℝ` countably. -/
lemma rational_ioo_isCountablySpanning :
    IsCountablySpanning
      (⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ioo (a : ℝ) (b : ℝ)} : Set (Set ℝ))) := by
  -- The intervals `(-n, n)` already cover the line.
  refine ⟨fun n ↦ Ioo (-(n + 1 : ℝ)) (n + 1 : ℝ), ?_, ?_⟩
  · intro n
    exact mem_iUnion.2
      ⟨-(n + 1 : ℚ), mem_iUnion.2 ⟨n + 1, mem_iUnion.2 ⟨by linarith, by simp⟩⟩⟩
  · ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      have hmem : x ∈ Ioo (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
        have h' : -(n : ℝ) < x ∧ x < (n : ℝ) := by
          simpa [abs_lt] using hn
        constructor
        · linarith
        · linarith
      exact mem_iUnion.2 ⟨n, hmem⟩

/-- Helper for Theorem 1.23: rational half-open intervals `(a, b]` span `ℝ` countably. -/
lemma rational_ioc_isCountablySpanning :
    IsCountablySpanning
      (⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ioc (a : ℝ) (b : ℝ)} : Set (Set ℝ))) := by
  -- The intervals `(-n, n]` already cover the line.
  refine ⟨fun n ↦ Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ), ?_, ?_⟩
  · intro n
    exact mem_iUnion.2
      ⟨-(n + 1 : ℚ), mem_iUnion.2 ⟨n + 1, mem_iUnion.2 ⟨by linarith, by simp⟩⟩⟩
  · ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      have hmem : x ∈ Ioc (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
        have h' : -(n : ℝ) < x ∧ x < (n : ℝ) := by
          simpa [abs_lt] using hn
        constructor
        · linarith
        · linarith
      exact mem_iUnion.2 ⟨n, hmem⟩

/-- Helper for Theorem 1.23: rational half-open intervals `[a, b)` span `ℝ` countably. -/
lemma rational_ico_isCountablySpanning :
    IsCountablySpanning
      (⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ico (a : ℝ) (b : ℝ)} : Set (Set ℝ))) := by
  -- The intervals `[-n, n)` already cover the line.
  refine ⟨fun n ↦ Ico (-(n + 1 : ℝ)) (n + 1 : ℝ), ?_, ?_⟩
  · intro n
    exact mem_iUnion.2
      ⟨-(n + 1 : ℚ), mem_iUnion.2 ⟨n + 1, mem_iUnion.2 ⟨by linarith, by simp⟩⟩⟩
  · ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      have h' : -(n : ℝ) < x ∧ x < (n : ℝ) := by
        simpa [abs_lt] using hn
      have hmem : x ∈ Ico (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
        constructor
        · linarith
        · linarith
      exact mem_iUnion.2 ⟨n, hmem⟩

/-- Helper for Theorem 1.23: rational intervals `(a, b]` generate the Borel
`σ`-algebra on `ℝ`. -/
lemma borel_real_eq_generateFrom_rational_ioc :
    borel ℝ =
      MeasurableSpace.generateFrom
        {S : Set ℝ | ∃ a b : ℚ, a < b ∧ Ioc (a : ℝ) (b : ℝ) = S} := by
  -- Apply the dense-endpoint interval theorem with the rational points.
  simpa [Set.mem_range] using
    (Rat.denseRange_cast.borel_eq_generateFrom_Ioc_mem (α := ℝ))

/-- Helper for Theorem 1.23: rational intervals `[a, b)` generate the Borel
`σ`-algebra on `ℝ`. -/
lemma borel_real_eq_generateFrom_rational_ico :
    borel ℝ =
      MeasurableSpace.generateFrom
        {S : Set ℝ | ∃ a b : ℚ, a < b ∧ Ico (a : ℝ) (b : ℝ) = S} := by
  -- Apply the dense-endpoint interval theorem with the rational points.
  simpa [Set.mem_range] using
    (Rat.denseRange_cast.borel_eq_generateFrom_Ico_mem (α := ℝ))

/-- Helper for Theorem 1.23: a closed interval is the intersection of shrinking left-open,
right-closed intervals. -/
lemma icc_eq_iInter_ioc_shrinking {a b : ℝ} :
    Icc a b = ⋂ n : ℕ, Ioc (a - 1 / (n + 1 : ℝ)) b := by
  -- The lower bound is recovered by letting the left endpoint approach `a`.
  ext x
  constructor
  · intro hx
    simp only [mem_iInter, mem_Ioc]
    intro n
    constructor
    · have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
        positivity
      linarith [hx.1, hpos]
    · exact hx.2
  · intro hx
    simp only [mem_iInter] at hx
    have hxb : x ≤ b := (hx 0).2
    have hxa : a ≤ x := by
      by_contra hax
      have hax' : 0 < a - x := sub_pos.2 (lt_of_not_ge hax)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hax'
      have hx_n := (hx n).1
      linarith
    exact ⟨hxa, hxb⟩

/-- Helper for Theorem 1.23: a left-open, right-closed interval is the union of increasing
expanding half-open intervals. -/
lemma iic_eq_iUnion_ioc_expanding (b : ℝ) :
    Iic b = ⋃ n : ℕ, Ioc (b - (n + 1 : ℝ)) b := by
  -- Move the left endpoint farther and farther to the left.
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt (b - x)
    refine mem_iUnion.2 ⟨n, ?_⟩
    simp only [mem_Ioc]
    constructor
    · linarith
    · exact hx
  · intro hx
    rcases mem_iUnion.1 hx with ⟨n, hn⟩
    exact hn.2

/-- Helper for Theorem 1.23: a closed interval is the union of expanding closed intervals. -/
lemma iic_eq_iUnion_icc_expanding (b : ℝ) :
    Iic b = ⋃ n : ℕ, Icc (b - (n + 1 : ℝ)) b := by
  -- Move the left endpoint farther and farther to the left.
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt (b - x)
    refine mem_iUnion.2 ⟨n, ?_⟩
    constructor
    · linarith
    · exact hx
  · intro hx
    rcases mem_iUnion.1 hx with ⟨n, hn⟩
    exact hn.2

/-- Helper for Theorem 1.23: a closed upper ray is the union of expanding `[a, b)` intervals. -/
lemma ici_eq_iUnion_ico_expanding (a : ℝ) :
    Ici a = ⋃ n : ℕ, Ico a (a + (n + 1 : ℝ)) := by
  -- Move the right endpoint farther and farther to the right.
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt (x - a)
    refine mem_iUnion.2 ⟨n, ?_⟩
    constructor
    · exact hx
    · linarith
  · intro hx
    rcases mem_iUnion.1 hx with ⟨n, hn⟩
    exact hn.1

/-- Helper for Theorem 1.23: a rational closed rectangle is the intersection of shrinking
left-open, right-closed rational rectangles. -/
lemma closed_rectangle_eq_iInter_ioc_rectangles (n : ℕ) (a b : Fin n → ℚ) :
    {x : Fin n → ℝ | ∀ j, (a j : ℝ) ≤ x j ∧ x j ≤ (b j : ℝ)} =
      ⋂ m : ℕ,
        {x : Fin n → ℝ |
          ∀ j, (a j : ℝ) - 1 / (m + 1 : ℝ) < x j ∧ x j ≤ (b j : ℝ)} := by
  -- Apply the one-dimensional approximation in each coordinate.
  ext x
  constructor
  · intro hx
    simp only [mem_iInter]
    intro m j
    constructor
    · have hpos : (0 : ℝ) < 1 / (m + 1 : ℝ) := by
        positivity
      linarith [(hx j).1, hpos]
    · exact (hx j).2
  · intro hx
    simp only [mem_iInter] at hx
    intro j
    have hxj : x j ∈ Icc (a j : ℝ) (b j : ℝ) := by
      simpa [icc_eq_iInter_ioc_shrinking, Set.mem_iInter] using
        (fun m : ℕ => hx m j)
    simpa using hxj

/-- Helper for Theorem 1.23: a rational closed lower orthant is the union of expanding
left-open, right-closed rectangles. -/
lemma closed_lower_orthant_eq_iUnion_ioc_rectangles (n : ℕ) (b : Fin n → ℚ) :
    {x : Fin n → ℝ | ∀ j, x j ≤ (b j : ℝ)} =
      ⋃ m : ℕ,
        {x : Fin n → ℝ | ∀ j, (b j : ℝ) - (m + 1 : ℝ) < x j ∧ x j ≤ (b j : ℝ)} := by
  -- Use the one-dimensional decomposition coordinatewise and synchronize the index by `sup`.
  ext x
  constructor
  · intro hx
    have hxj : ∀ j : Fin n, x j ∈ ⋃ m : ℕ, Ioc ((b j : ℝ) - (m + 1 : ℝ)) (b j : ℝ) := by
      intro j
      rw [← iic_eq_iUnion_ioc_expanding]
      exact hx j
    choose m hm using fun j => mem_iUnion.1 (hxj j)
    let M : ℕ := Finset.univ.sup m
    refine mem_iUnion.2 ⟨M, ?_⟩
    intro j
    have hmj := hm j
    have hle : m j ≤ M := by
      dsimp [M]
      exact Finset.le_sup (Finset.mem_univ j)
    constructor
    · have hshift :
          (b j : ℝ) - (M + 1 : ℝ) ≤ (b j : ℝ) - (m j + 1 : ℝ) := by
        have hle' : (m j : ℝ) + 1 ≤ (M : ℝ) + 1 := by
          exact_mod_cast Nat.succ_le_succ hle
        linarith
      exact lt_of_le_of_lt hshift hmj.1
    · exact hmj.2
  · intro hx
    rcases mem_iUnion.1 hx with ⟨m, hm⟩
    intro j
    exact (hm j).2

/-- Helper for Theorem 1.23: a rational closed lower orthant is the union of expanding
closed rectangles. -/
lemma closed_lower_orthant_eq_iUnion_closed_rectangles (n : ℕ) (b : Fin n → ℚ) :
    {x : Fin n → ℝ | ∀ j, x j ≤ (b j : ℝ)} =
      ⋃ m : ℕ,
        {x : Fin n → ℝ | ∀ j, (b j : ℝ) - (m + 1 : ℝ) ≤ x j ∧ x j ≤ (b j : ℝ)} := by
  -- Use the one-dimensional closed-interval decomposition coordinatewise.
  ext x
  constructor
  · intro hx
    have hxj : ∀ j : Fin n, x j ∈ ⋃ m : ℕ, Icc ((b j : ℝ) - (m + 1 : ℝ)) (b j : ℝ) := by
      intro j
      rw [← iic_eq_iUnion_icc_expanding]
      exact hx j
    choose m hm using fun j => mem_iUnion.1 (hxj j)
    let M : ℕ := Finset.univ.sup m
    refine mem_iUnion.2 ⟨M, ?_⟩
    intro j
    have hmj := hm j
    have hle : m j ≤ M := by
      dsimp [M]
      exact Finset.le_sup (Finset.mem_univ j)
    constructor
    · have hshift :
          (b j : ℝ) - (M + 1 : ℝ) ≤ (b j : ℝ) - (m j + 1 : ℝ) := by
        have hle' : (m j : ℝ) + 1 ≤ (M : ℝ) + 1 := by
          exact_mod_cast Nat.succ_le_succ hle
        linarith
      exact hshift.trans hmj.1
    · exact hmj.2
  · intro hx
    rcases mem_iUnion.1 hx with ⟨m, hm⟩
    intro j
    exact (hm j).2

/-- Helper for Theorem 1.23: a rational closed upper orthant is the union of expanding
left-closed, right-open rectangles. -/
lemma closed_upper_orthant_eq_iUnion_ico_rectangles (n : ℕ) (a : Fin n → ℚ) :
    {x : Fin n → ℝ | ∀ j, (a j : ℝ) ≤ x j} =
      ⋃ m : ℕ,
        {x : Fin n → ℝ | ∀ j, (a j : ℝ) ≤ x j ∧ x j < (a j : ℝ) + (m + 1 : ℝ)} := by
  -- Use the one-dimensional upper-ray decomposition coordinatewise.
  ext x
  constructor
  · intro hx
    have hxj : ∀ j : Fin n, x j ∈ ⋃ m : ℕ, Ico (a j : ℝ) ((a j : ℝ) + (m + 1 : ℝ)) := by
      intro j
      rw [← ici_eq_iUnion_ico_expanding]
      exact hx j
    choose m hm using fun j => mem_iUnion.1 (hxj j)
    let M : ℕ := Finset.univ.sup m
    refine mem_iUnion.2 ⟨M, ?_⟩
    intro j
    have hmj := hm j
    have hle : m j ≤ M := by
      dsimp [M]
      exact Finset.le_sup (Finset.mem_univ j)
    constructor
    · exact hmj.1
    · have hshift : (a j : ℝ) + (m j + 1 : ℝ) ≤ (a j : ℝ) + (M + 1 : ℝ) := by
        have hle' : (m j : ℝ) + 1 ≤ (M : ℝ) + 1 := by
          exact_mod_cast Nat.succ_le_succ hle
        linarith
      exact lt_of_lt_of_le hmj.2 hshift
  · intro hx
    rcases mem_iUnion.1 hx with ⟨m, hm⟩
    intro j
    exact (hm j).1

/-- Helper for Theorem 1.23: rational open balls form a topological basis on `ℝⁿ`. -/
lemma rational_open_balls_isTopologicalBasis (n : ℕ) :
    IsTopologicalBasis (euclideanBorelGeneratorClass n .rationalOpenBalls) := by
  let e : EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
  have h_dense : DenseRange (fun c : Fin n → ℚ ↦ e.symm (fun j ↦ (c j : ℝ))) := by
    exact DenseRange.comp
      e.symm.surjective.denseRange
      (DenseRange.piMap fun _ : Fin n ↦ Rat.denseRange_cast)
      e.symm.continuous
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro s ⟨c, r, hr, rfl⟩
    exact (e.isOpen_image (s := Metric.ball (e.symm (fun j ↦ (c j : ℝ))) (r : ℝ))).2 isOpen_ball
  · intro x u hx hu
    let y : EuclideanSpace ℝ (Fin n) := e.symm x
    have hyu : y ∈ e ⁻¹' u := hx
    have hpre : IsOpen (e ⁻¹' u) := e.isOpen_preimage.mpr hu
    rcases Metric.mem_nhds_iff.1 (hpre.mem_nhds hyu) with ⟨ε, hε, hεu⟩
    have hquarter : 0 < ε / 4 := by
      positivity
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hquarter
    rcases Metric.denseRange_iff.1 h_dense y (q : ℝ)
        (show 0 < (q : ℝ) by exact_mod_cast hq0) with ⟨c, hyc⟩
    have hyc' : dist y (e.symm (fun j ↦ (c j : ℝ))) < q := by
      simpa [dist_comm] using hyc
    have hyc'' : dist (e.symm (fun j ↦ (c j : ℝ))) y < q := by
      simpa [dist_comm] using hyc'
    obtain ⟨r, hyr, hrq⟩ := exists_rat_btwn (lt_trans hyc' hqε)
    refine ⟨e '' Metric.ball (e.symm (fun j ↦ (c j : ℝ))) (r : ℝ), ⟨c, r, ?_, rfl⟩, ?_, ?_⟩
    · exact_mod_cast (lt_of_le_of_lt dist_nonneg hyr)
    · refine ⟨y, ?_, ?_⟩
      · simpa [Metric.mem_ball, dist_comm] using hyr
      · simpa [y, e] using e.apply_symm_apply x
    · intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      have hwy : dist w y < ε := by
        have hdist : dist w y < (r : ℝ) + q := by
          exact lt_of_le_of_lt (dist_triangle w (e.symm (fun j ↦ (c j : ℝ))) y)
            (add_lt_add hw hyc'')
        linarith
      exact hεu (by simpa [Metric.mem_ball, dist_comm] using hwy)

/-- Helper for Theorem 1.23: every rational closed rectangle in `ℝⁿ` is compact. -/
lemma rational_closed_rectangle_isCompact (n : ℕ) (a b : Fin n → ℚ) :
    IsCompact {x : Fin n → ℝ | ∀ j, (a j : ℝ) ≤ x j ∧ x j ≤ (b j : ℝ)} := by
  -- Rewrite the rectangle as an order interval in the product order.
  have hset :
      {x : Fin n → ℝ | ∀ j, (a j : ℝ) ≤ x j ∧ x j ≤ (b j : ℝ)} =
        Icc (fun j ↦ (a j : ℝ)) (fun j ↦ (b j : ℝ)) := by
    ext x
    constructor
    · intro hx
      constructor
      · intro j
        exact (hx j).1
      · intro j
        exact (hx j).2
    · intro hx j
      exact ⟨hx.1 j, hx.2 j⟩
  rw [hset]
  exact isCompact_Icc

/-- The open-set case of `euclideanBorelGeneratorClass` is exactly the topology of open subsets
of `ℝⁿ`. -/
-- Proof sketch: unfold `euclideanBorelGeneratorClass` at the `openSets` constructor.
theorem euclideanBorelGeneratorClass_openSets (n : ℕ) :
    euclideanBorelGeneratorClass n .openSets = {s : Set (Fin n → ℝ) | IsOpen s} := by
  -- Unfolding the constructor gives the target family immediately.
  rfl

/-- Theorem 1.23: For each of the twelve classes `E₁, …, E₁₂` of subsets of `ℝⁿ`, the Borel
`σ`-algebra on `ℝⁿ` is the measurable space generated by that class. Here `ℝⁿ` is modeled as
`Fin n → ℝ`, and the constructors of `EuclideanBorelGenerator` enumerate `E₁, …, E₁₂` in
order. -/
-- Proof sketch: prove the open-set case from the definition of `borel`, then show each of the
-- other eleven generator classes yields the same generated measurable space by the standard
-- exhaustion and approximation arguments with rational balls and rational rectangles.
theorem borel_eq_generateFrom_euclideanBorelGeneratorClass (n : ℕ)
    (i : EuclideanBorelGenerator) :
    borel (Fin n → ℝ) = MeasurableSpace.generateFrom (euclideanBorelGeneratorClass n i) := by
  -- First identify the coordinatewise product descriptions of the generator families.
  have h_open_lower_family :
      euclideanBorelGeneratorClass n .rationalOpenLowerOrthants =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n => ⋃ q : ℚ, ({Iio (q : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_single_endpoint_generator_eq_pi (n := n) (F := fun q ↦ Iio (q : ℝ))
  have h_closed_lower_family :
      euclideanBorelGeneratorClass n .rationalClosedLowerOrthants =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n => ⋃ q : ℚ, ({Iic (q : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_single_endpoint_generator_eq_pi (n := n) (F := fun q ↦ Iic (q : ℝ))
  have h_open_upper_family :
      euclideanBorelGeneratorClass n .rationalOpenUpperOrthants =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n => ⋃ q : ℚ, ({Ioi (q : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_single_endpoint_generator_eq_pi (n := n) (F := fun q ↦ Ioi (q : ℝ))
  have h_closed_upper_family :
      euclideanBorelGeneratorClass n .rationalClosedUpperOrthants =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n => ⋃ q : ℚ, ({Ici (q : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_single_endpoint_generator_eq_pi (n := n) (F := fun q ↦ Ici (q : ℝ))
  have h_open_rectangles_family :
      euclideanBorelGeneratorClass n .rationalOpenRectangles =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n =>
            ⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ioo (a : ℝ) (b : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_two_endpoint_generator_eq_pi (n := n) (F := fun a b ↦ Ioo (a : ℝ) (b : ℝ))
  have h_ioc_rectangles_family :
      euclideanBorelGeneratorClass n .rationalLeftOpenRightClosedRectangles =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n =>
            ⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ioc (a : ℝ) (b : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_two_endpoint_generator_eq_pi (n := n) (F := fun a b ↦ Ioc (a : ℝ) (b : ℝ))
  have h_ico_rectangles_family :
      euclideanBorelGeneratorClass n .rationalLeftClosedRightOpenRectangles =
        Set.pi univ '' Set.pi univ
          (fun _ : Fin n =>
            ⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ico (a : ℝ) (b : ℝ)} : Set (Set ℝ))) := by
    simpa [euclideanBorelGeneratorClass] using
      rational_two_endpoint_generator_eq_pi (n := n) (F := fun a b ↦ Ico (a : ℝ) (b : ℝ))
  -- Next prove the product-generator cases directly from the one-dimensional theorems.
  have h_open_lower :
      borel (Fin n → ℝ) =
        MeasurableSpace.generateFrom
          (euclideanBorelGeneratorClass n .rationalOpenLowerOrthants) := by
    rw [h_open_lower_family]
    exact borel_eq_generateFrom_pi_boxes n
      (⋃ q : ℚ, ({Iio (q : ℝ)} : Set (Set ℝ)))
      Real.borel_eq_generateFrom_Iio_rat
      rational_iio_isCountablySpanning
  have h_closed_lower :
      borel (Fin n → ℝ) =
        MeasurableSpace.generateFrom
          (euclideanBorelGeneratorClass n .rationalClosedLowerOrthants) := by
    rw [h_closed_lower_family]
    exact borel_eq_generateFrom_pi_boxes n
      (⋃ q : ℚ, ({Iic (q : ℝ)} : Set (Set ℝ)))
      Real.borel_eq_generateFrom_Iic_rat
      rational_iic_isCountablySpanning
  have h_open_upper :
      borel (Fin n → ℝ) =
        MeasurableSpace.generateFrom
          (euclideanBorelGeneratorClass n .rationalOpenUpperOrthants) := by
    rw [h_open_upper_family]
    exact borel_eq_generateFrom_pi_boxes n
      (⋃ q : ℚ, ({Ioi (q : ℝ)} : Set (Set ℝ)))
      Real.borel_eq_generateFrom_Ioi_rat
      rational_ioi_isCountablySpanning
  have h_closed_upper :
      borel (Fin n → ℝ) =
        MeasurableSpace.generateFrom
          (euclideanBorelGeneratorClass n .rationalClosedUpperOrthants) := by
    rw [h_closed_upper_family]
    exact borel_eq_generateFrom_pi_boxes n
      (⋃ q : ℚ, ({Ici (q : ℝ)} : Set (Set ℝ)))
      Real.borel_eq_generateFrom_Ici_rat
      rational_ici_isCountablySpanning
  have h_open_rectangles :
      borel (Fin n → ℝ) =
        MeasurableSpace.generateFrom
          (euclideanBorelGeneratorClass n .rationalOpenRectangles) := by
    rw [h_open_rectangles_family]
    exact borel_eq_generateFrom_pi_boxes n
      (⋃ a : ℚ, ⋃ b : ℚ, ⋃ (_ : a < b), ({Ioo (a : ℝ) (b : ℝ)} : Set (Set ℝ)))
      Real.borel_eq_generateFrom_Ioo_rat
      rational_ioo_isCountablySpanning
  have h_ioc_rectangles :
      borel (Fin n → ℝ) =
        MeasurableSpace.generateFrom
          (euclideanBorelGeneratorClass n .rationalLeftOpenRightClosedRectangles) := by
    have h_gen_le_borel :
        MeasurableSpace.generateFrom
            (euclideanBorelGeneratorClass n .rationalLeftOpenRightClosedRectangles) ≤
          borel (Fin n → ℝ) := by
      -- Each `(a, b]` rectangle is an open-upper orthant intersected with a closed-lower orthant.
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨a, b, hab, rfl⟩
      have hopen :
          MeasurableSet[borel (Fin n → ℝ)] {x : Fin n → ℝ | ∀ j, (a j : ℝ) < x j} := by
        rw [h_open_upper]
        exact measurableSet_generateFrom ⟨a, rfl⟩
      have hclosed :
          MeasurableSet[borel (Fin n → ℝ)] {x : Fin n → ℝ | ∀ j, x j ≤ (b j : ℝ)} := by
        rw [h_closed_lower]
        exact measurableSet_generateFrom ⟨b, rfl⟩
      have hs :
          {x : Fin n → ℝ | ∀ j, (a j : ℝ) < x j ∧ x j ≤ (b j : ℝ)} =
            {x : Fin n → ℝ | ∀ j, (a j : ℝ) < x j} ∩
              {x : Fin n → ℝ | ∀ j, x j ≤ (b j : ℝ)} := by
        ext x
        constructor
        · intro hx
          exact ⟨fun j ↦ (hx j).1, fun j ↦ (hx j).2⟩
        · rintro ⟨hx₁, hx₂⟩ j
          exact ⟨hx₁ j, hx₂ j⟩
      rw [hs]
      exact hopen.inter hclosed
    have h_borel_le_gen :
        borel (Fin n → ℝ) ≤
          MeasurableSpace.generateFrom
            (euclideanBorelGeneratorClass n .rationalLeftOpenRightClosedRectangles) := by
      calc
        borel (Fin n → ℝ) =
            MeasurableSpace.generateFrom
              (euclideanBorelGeneratorClass n .rationalClosedLowerOrthants) :=
          h_closed_lower
        _ ≤ MeasurableSpace.generateFrom
              (euclideanBorelGeneratorClass n .rationalLeftOpenRightClosedRectangles) := by
          refine MeasurableSpace.generateFrom_le ?_
          rintro s ⟨b, rfl⟩
          rw [closed_lower_orthant_eq_iUnion_ioc_rectangles n b]
          refine MeasurableSet.iUnion ?_
          intro m
          apply measurableSet_generateFrom
          refine ⟨fun j ↦ b j - (m + 1 : ℚ), b, ?_, ?_⟩
          · intro j
            have hpos : (0 : ℚ) < (m + 1 : ℚ) := by positivity
            linarith
          · ext x
            simp
    exact le_antisymm h_borel_le_gen h_gen_le_borel
  have h_ico_rectangles :
      borel (Fin n → ℝ) =
        MeasurableSpace.generateFrom
          (euclideanBorelGeneratorClass n .rationalLeftClosedRightOpenRectangles) := by
    have h_gen_le_borel :
        MeasurableSpace.generateFrom
            (euclideanBorelGeneratorClass n .rationalLeftClosedRightOpenRectangles) ≤
          borel (Fin n → ℝ) := by
      -- Each `[a, b)` rectangle is a closed-upper orthant intersected with an open-lower orthant.
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨a, b, hab, rfl⟩
      have hclosed :
          MeasurableSet[borel (Fin n → ℝ)] {x : Fin n → ℝ | ∀ j, (a j : ℝ) ≤ x j} := by
        rw [h_closed_upper]
        exact measurableSet_generateFrom ⟨a, rfl⟩
      have hopen :
          MeasurableSet[borel (Fin n → ℝ)] {x : Fin n → ℝ | ∀ j, x j < (b j : ℝ)} := by
        rw [h_open_lower]
        exact measurableSet_generateFrom ⟨b, rfl⟩
      have hs :
          {x : Fin n → ℝ | ∀ j, (a j : ℝ) ≤ x j ∧ x j < (b j : ℝ)} =
            {x : Fin n → ℝ | ∀ j, (a j : ℝ) ≤ x j} ∩
              {x : Fin n → ℝ | ∀ j, x j < (b j : ℝ)} := by
        ext x
        constructor
        · intro hx
          exact ⟨fun j ↦ (hx j).1, fun j ↦ (hx j).2⟩
        · rintro ⟨hx₁, hx₂⟩ j
          exact ⟨hx₁ j, hx₂ j⟩
      rw [hs]
      exact hclosed.inter hopen
    have h_borel_le_gen :
        borel (Fin n → ℝ) ≤
          MeasurableSpace.generateFrom
            (euclideanBorelGeneratorClass n .rationalLeftClosedRightOpenRectangles) := by
      calc
        borel (Fin n → ℝ) =
            MeasurableSpace.generateFrom
              (euclideanBorelGeneratorClass n .rationalClosedUpperOrthants) :=
          h_closed_upper
        _ ≤ MeasurableSpace.generateFrom
              (euclideanBorelGeneratorClass n .rationalLeftClosedRightOpenRectangles) := by
          refine MeasurableSpace.generateFrom_le ?_
          rintro s ⟨a, rfl⟩
          rw [closed_upper_orthant_eq_iUnion_ico_rectangles n a]
          refine MeasurableSet.iUnion ?_
          intro m
          apply measurableSet_generateFrom
          refine ⟨a, fun j ↦ a j + (m + 1 : ℚ), ?_, ?_⟩
          · intro j
            have hpos : (0 : ℚ) < (m + 1 : ℚ) := by positivity
            linarith
          · ext x
            simp
    exact le_antisymm h_borel_le_gen h_gen_le_borel
  -- Then recover the remaining non-product generators from these stable cases.
  have h_closed_rectangles :
      borel (Fin n → ℝ) =
        MeasurableSpace.generateFrom
          (euclideanBorelGeneratorClass n .rationalClosedRectangles) := by
    have h_gen_le_borel :
        MeasurableSpace.generateFrom
            (euclideanBorelGeneratorClass n .rationalClosedRectangles) ≤
          borel (Fin n → ℝ) := by
      -- Each closed rectangle is the intersection of a closed upper and a closed lower orthant.
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨a, b, hab, rfl⟩
      have hs :
          {x : Fin n → ℝ |
              ∀ j, (a j : ℝ) ≤ x j ∧ x j ≤ (b j : ℝ)} =
            {x : Fin n → ℝ |
              ∀ j, (a j : ℝ) ≤ x j} ∩
                {x : Fin n → ℝ | ∀ j, x j ≤ (b j : ℝ)} := by
        ext x
        constructor
        · intro hx
          exact ⟨fun j ↦ (hx j).1, fun j ↦ (hx j).2⟩
        · rintro ⟨hx₁, hx₂⟩ j
          exact ⟨hx₁ j, hx₂ j⟩
      rw [hs]
      have hupper :
          MeasurableSet[borel (Fin n → ℝ)] {x : Fin n → ℝ | ∀ j, (a j : ℝ) ≤ x j} := by
        rw [h_closed_upper]
        exact measurableSet_generateFrom ⟨a, rfl⟩
      have hlower :
          MeasurableSet[borel (Fin n → ℝ)] {x : Fin n → ℝ | ∀ j, x j ≤ (b j : ℝ)} := by
        rw [h_closed_lower]
        exact measurableSet_generateFrom ⟨b, rfl⟩
      exact hupper.inter hlower
    have h_borel_le_gen :
        borel (Fin n → ℝ) ≤
          MeasurableSpace.generateFrom
            (euclideanBorelGeneratorClass n .rationalClosedRectangles) := by
      calc
        borel (Fin n → ℝ) =
            MeasurableSpace.generateFrom
              (euclideanBorelGeneratorClass n .rationalClosedLowerOrthants) :=
          h_closed_lower
        _ ≤ MeasurableSpace.generateFrom
              (euclideanBorelGeneratorClass n .rationalClosedRectangles) := by
          refine MeasurableSpace.generateFrom_le ?_
          rintro s ⟨b, rfl⟩
          rw [closed_lower_orthant_eq_iUnion_closed_rectangles n b]
          refine MeasurableSet.iUnion ?_
          intro m
          apply measurableSet_generateFrom
          refine ⟨fun j ↦ b j - (m + 1 : ℚ), b, ?_, ?_⟩
          · intro j
            have hpos : (0 : ℚ) < (m + 1 : ℚ) := by positivity
            linarith
          · ext x
            simp
    exact le_antisymm h_borel_le_gen h_gen_le_borel
  have h_compact :
      borel (Fin n → ℝ) =
        MeasurableSpace.generateFrom
          (euclideanBorelGeneratorClass n .compactSets) := by
    have h_compact_le_borel :
        MeasurableSpace.generateFrom
            (euclideanBorelGeneratorClass n .compactSets) ≤
          borel (Fin n → ℝ) := by
      -- Compact sets are closed in the Hausdorff space `ℝⁿ`, hence Borel.
      refine MeasurableSpace.generateFrom_le ?_
      intro s hs
      rw [← BorelSpace.measurable_eq (α := Fin n → ℝ)]
      exact hs.isClosed.measurableSet
    have h_borel_le_compact :
        borel (Fin n → ℝ) ≤
          MeasurableSpace.generateFrom
            (euclideanBorelGeneratorClass n .compactSets) := by
      calc
        borel (Fin n → ℝ) =
            MeasurableSpace.generateFrom
              (euclideanBorelGeneratorClass n .rationalClosedRectangles) :=
          h_closed_rectangles
        _ ≤ MeasurableSpace.generateFrom
              (euclideanBorelGeneratorClass n .compactSets) := by
          apply MeasurableSpace.generateFrom_mono
          rintro s ⟨a, b, hab, rfl⟩
          simpa [euclideanBorelGeneratorClass] using
            rational_closed_rectangle_isCompact n a b
    exact le_antisymm h_borel_le_compact h_compact_le_borel
  have h_open_balls :
      borel (Fin n → ℝ) =
        MeasurableSpace.generateFrom
          (euclideanBorelGeneratorClass n .rationalOpenBalls) := by
    -- Rational balls form a countable topological basis of `ℝⁿ`.
    exact (rational_open_balls_isTopologicalBasis n).borel_eq_generateFrom
  -- Finish by selecting the pre-proved case corresponding to the chosen generator.
  cases i with
  | openSets =>
      -- This case is exactly the definition of the Borel `σ`-algebra.
      rw [euclideanBorelGeneratorClass_openSets]
      rfl
  | closedSets =>
      -- Closed sets generate the same Borel `σ`-algebra by complements.
      simpa [euclideanBorelGeneratorClass] using
        (borel_eq_generateFrom_isClosed (α := Fin n → ℝ))
  | compactSets =>
      exact h_compact
  | rationalOpenBalls =>
      exact h_open_balls
  | rationalOpenRectangles =>
      exact h_open_rectangles
  | rationalClosedRectangles =>
      exact h_closed_rectangles
  | rationalLeftOpenRightClosedRectangles =>
      exact h_ioc_rectangles
  | rationalLeftClosedRightOpenRectangles =>
      exact h_ico_rectangles
  | rationalOpenLowerOrthants =>
      exact h_open_lower
  | rationalClosedLowerOrthants =>
      exact h_closed_lower
  | rationalOpenUpperOrthants =>
      exact h_open_upper
  | rationalClosedUpperOrthants =>
      exact h_closed_upper
