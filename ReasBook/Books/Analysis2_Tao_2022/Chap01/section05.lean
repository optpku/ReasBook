/-
Authors: Zichen Wang, Wanli Ma, Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap01
section Section05

/-- Definition 1.21: A subset `X ⊆ ℝ` is sequentially compact if every sequence in `X` has a
convergent subsequence whose limit belongs to `X`. -/
abbrev IsSequentiallyCompact (X : Set ℝ) : Prop :=
  IsSeqCompact X

/-- The book's sequential compactness is the same as `IsSeqCompact`. -/
lemma isSequentiallyCompact_iff_isSeqCompact (X : Set ℝ) :
    IsSequentiallyCompact X ↔ IsSeqCompact X := by
  rfl

/-- Theorem 1.5 (Heine--Borel theorem on `ℝ`): For `X ⊆ ℝ`, the following are equivalent:
    (i) `X` is closed and bounded.
    (ii) Every sequence `(x_n)` in `X` has a subsequence `(x_{n_k})` converging to a limit `x ∈ X`. -/
theorem heineBorel_real_iff_isSequentiallyCompact (X : Set ℝ) :
    (IsClosed X ∧ Bornology.IsBounded X) ↔ IsSequentiallyCompact X := by
  have hcompact : IsCompact X ↔ IsClosed X ∧ Bornology.IsBounded X := by
    simpa using (Metric.isCompact_iff_isClosed_bounded (s := X))
  have hseq : IsCompact X ↔ IsSeqCompact X := by
    simpa using (UniformSpace.isCompact_iff_isSeqCompact (s := X))
  simpa [IsSequentiallyCompact] using hcompact.symm.trans hseq

/-- Definition 1.22 (Compactness): A metric space `(X,d)` is compact if every sequence `(x_n)` in
`X` has a strictly increasing `k : ℕ → ℕ` and a point `x ∈ X` with `d (x_{k(n)}) x → 0`. A subset
`Y ⊆ X` is compact in `X` if the induced metric on `Y` is compact. -/
abbrev IsSequentiallyCompactSpace (X : Type*) [MetricSpace X] : Prop :=
  SeqCompactSpace X

/-- Book's compactness of a metric space, expressed as sequential compactness. -/
abbrev IsCompactSpace (X : Type*) [MetricSpace X] : Prop :=
  IsSequentiallyCompactSpace (X:=X)

/-- The book's compactness of a metric space is equivalent to `SeqCompactSpace`. -/
lemma isCompactSpace_iff_seqCompactSpace (X : Type*) [MetricSpace X] :
    IsCompactSpace X ↔ SeqCompactSpace X := by
  rfl

/-- Book's compactness for a subset of a metric space, expressed as `IsSeqCompact`. -/
abbrev IsCompactSubset {X : Type*} [MetricSpace X] (Y : Set X) : Prop :=
  IsSeqCompact Y

/-- The book's compact subset notion is equivalent to `IsSeqCompact`. -/
lemma isCompactSubset_iff_isSeqCompact {X : Type*} [MetricSpace X] (Y : Set X) :
    IsCompactSubset (X:=X) Y ↔ IsSeqCompact Y := by
  rfl

/-- Definition 1.23 (Bounded sets): In a metric space `(X,d)`, a subset `Y` is bounded if there
exist `x ∈ X` and `r ∈ ℝ` with `0 ≤ r < ∞` such that `Y ⊆ B(x,r) = {y ∈ X : d(x,y) < r}`. The
metric space `(X,d)` is bounded if the set `X` is bounded. -/
def IsBoundedSubset {X : Type*} [MetricSpace X] (Y : Set X) : Prop :=
  Y = ∅ ∨ ∃ x : X, ∃ r : ℝ, 0 ≤ r ∧ Y ⊆ Metric.ball x r

/-- The book's boundedness for subsets agrees with `Bornology.IsBounded`. -/
lemma isBoundedSubset_iff_isBounded {X : Type*} [MetricSpace X] (Y : Set X) :
    IsBoundedSubset (X:=X) Y ↔ Bornology.IsBounded Y := by
  classical
  constructor
  · intro h
    rcases h with hY | hY
    · subst hY
      simpa using (Bornology.isBounded_empty : Bornology.IsBounded (∅ : Set X))
    · rcases hY with ⟨x, r, _, hsub⟩
      exact (Metric.isBounded_ball (x := x) (r := r)).subset hsub
  · intro h
    by_cases hY : Y = ∅
    · exact Or.inl hY
    · have hne : Y.Nonempty := Set.nonempty_iff_ne_empty.2 hY
      rcases hne with ⟨x, hx⟩
      rcases (h.subset_ball_lt 0 x) with ⟨r, hrpos, hsub⟩
      have hr0 : 0 ≤ r := le_of_lt hrpos
      exact Or.inr ⟨x, r, hr0, hsub⟩

/-- A metric space is bounded if it is a `BoundedSpace`. -/
abbrev IsBoundedSpace (X : Type*) [MetricSpace X] : Prop :=
  BoundedSpace X

/-- The book's boundedness of a metric space matches `BoundedSpace`. -/
lemma isBoundedSpace_iff_boundedSpace (X : Type*) [MetricSpace X] :
    IsBoundedSpace X ↔ BoundedSpace X := Iff.rfl

/-- A metric space is bounded iff its underlying set is bounded in the book's sense. -/
lemma isBoundedSpace_iff_isBounded_univ (X : Type*) [MetricSpace X] :
    IsBoundedSpace X ↔ IsBoundedSubset (X:=X) (Set.univ : Set X) := by
  classical
  calc
    IsBoundedSpace X ↔ BoundedSpace X := Iff.rfl
    _ ↔ Bornology.IsBounded (Set.univ : Set X) :=
      (Bornology.isBounded_univ (α := X)).symm
    _ ↔ IsBoundedSubset (X:=X) (Set.univ : Set X) :=
      (isBoundedSubset_iff_isBounded (X := X) (Y := Set.univ)).symm

/-- Definition 1.24: In a metric space `(X,d)`, a subset `K ⊆ X` is compact if every open cover
of `K` has a finite subcover; i.e. for every family of open sets `(U_i)_{i ∈ I}` in `X` with
`K ⊆ ⋃ i, U_i`, there exist indices `i₁, …, iₙ ∈ I` such that
`K ⊆ U_{i₁} ∪ … ∪ U_{iₙ}`. -/
abbrev IsCompactOpenCover {X : Type*} [MetricSpace X] (K : Set X) : Prop :=
  IsCompact K

/-- The book's open-cover compactness for subsets agrees with `IsCompact`. -/
lemma isCompactOpenCover_iff_isCompact {X : Type*} [MetricSpace X] (K : Set X) :
    IsCompactOpenCover (X:=X) K ↔ IsCompact K := Iff.rfl

/-- Definition 1.25 (Compactness via open covers): A topological space `Y` is compact if every
open cover of `Y` has a finite subcover. -/
abbrev IsCompactOpenCoverSpace (Y : Type*) [TopologicalSpace Y] : Prop :=
  CompactSpace Y

/-- The book's open-cover compactness for a space agrees with `CompactSpace`. -/
lemma isCompactOpenCoverSpace_iff_compactSpace (Y : Type*) [TopologicalSpace Y] :
    IsCompactOpenCoverSpace Y ↔ CompactSpace Y := Iff.rfl

/-- Definition 1.26: A metric space `(X,d)` is totally bounded if for every `ε > 0` there exist
`n ∈ ℕ` and points `x^(1), …, x^(n) ∈ X` such that `X = ⋃_{i=1}^n B(x^(i), ε)`. -/
abbrev IsTotallyBoundedSpace (X : Type*) [MetricSpace X] : Prop :=
  TotallyBounded (Set.univ : Set X)

/-- The book's totally boundedness is equivalent to a finite cover by metric balls. -/
lemma isTotallyBoundedSpace_iff_ball_cover (X : Type*) [MetricSpace X] :
    IsTotallyBoundedSpace X ↔
      ∀ ε > 0, ∃ t : Set X, t.Finite ∧
        (Set.univ : Set X) ⊆ ⋃ x ∈ t, Metric.ball x ε := by
  simpa [IsTotallyBoundedSpace] using
    (Metric.totallyBounded_iff (s := (Set.univ : Set X)))

/-- Helper for Proposition 1.28: sequential compactness of the book gives `CompactSpace`. -/
lemma helperForProposition_1_28_compactSpace_of_isCompactSpace (X : Type*) [MetricSpace X]
    (hX : IsCompactSpace X) : CompactSpace X := by
  have hseq : SeqCompactSpace X := hX
  exact (UniformSpace.compactSpace_iff_seqCompactSpace (X := X)).2 hseq

/-- Helper for Proposition 1.28: compact metric spaces are complete. -/
lemma helperForProposition_1_28_completeSpace_of_compactSpace (X : Type*) [MetricSpace X]
    [CompactSpace X] : CompleteSpace X := by
  infer_instance

/-- Helper for Proposition 1.28: compact metric spaces are bounded. -/
lemma helperForProposition_1_28_boundedSpace_of_compactSpace (X : Type*) [MetricSpace X]
    [CompactSpace X] : BoundedSpace X := by
  have hcompact : IsCompact (Set.univ : Set X) := isCompact_univ
  have hbounded : Bornology.IsBounded (Set.univ : Set X) := by
    simpa using hcompact.isBounded
  exact (Bornology.isBounded_univ (α := X)).1 hbounded

/-- Proposition 1.28: A compact metric space is complete and bounded. -/
theorem compactSpace_complete_and_bounded_prop (X : Type*) [MetricSpace X]
    (hX : IsCompactSpace X) : CompleteSpace X ∧ IsBoundedSpace X := by
  haveI : CompactSpace X :=
    helperForProposition_1_28_compactSpace_of_isCompactSpace (X := X) hX
  constructor
  · exact helperForProposition_1_28_completeSpace_of_compactSpace (X := X)
  · exact helperForProposition_1_28_boundedSpace_of_compactSpace (X := X)
/-- If a metric space is compact (in the book's sense), then it is complete and bounded. -/
theorem compactSpace_complete_and_bounded (X : Type*) [MetricSpace X]
    (hX : IsCompactSpace X) : CompleteSpace X ∧ IsBoundedSpace X := by
  simpa using compactSpace_complete_and_bounded_prop (X := X) hX

/-- Helper for Theorem 1.6: a compact subset of a metric space is closed. -/
lemma helperForTheorem_1_6_isClosed {X : Type*} [MetricSpace X] {Y : Set X}
    (hY : IsCompactSubset (X := X) Y) : IsClosed Y := by
  have hcompact : IsCompact Y := by
    have hseq : IsCompact Y ↔ IsSeqCompact Y := by
      simpa using (UniformSpace.isCompact_iff_isSeqCompact (s := Y))
    exact hseq.mpr hY
  exact hcompact.isClosed

/-- Theorem 1.6: (Compact subsets of metric spaces are closed and bounded) Let `(X,d)` be a metric
space and let `Y ⊆ X` be compact. Then: (i) `Y` is closed in `X`. (ii) `Y` is bounded, i.e. there
exist `x₀ ∈ X` and `R > 0` such that `Y ⊆ {x ∈ X : d x x₀ ≤ R}`. -/
theorem compactSubset_closed_and_bounded_prop {X : Type*} [MetricSpace X] {Y : Set X}
    (hY : IsCompactSubset (X := X) Y) : IsClosed Y ∧ IsBoundedSubset (X := X) Y := by
  constructor
  · exact helperForTheorem_1_6_isClosed (X := X) (Y := Y) hY
  ·
    have hcompact : IsCompact Y := by
      have hseq : IsCompact Y ↔ IsSeqCompact Y := by
        simpa using (UniformSpace.isCompact_iff_isSeqCompact (s := Y))
      exact hseq.mpr hY
    have hbounded : Bornology.IsBounded Y := hcompact.isBounded
    exact (isBoundedSubset_iff_isBounded (X := X) (Y := Y)).2 hbounded

/-- A compact subset of a metric space is closed and bounded. -/
theorem compactSubset_closed_and_bounded {X : Type*} [MetricSpace X] {Y : Set X}
    (hY : IsCompactSubset (X := X) Y) : IsClosed Y ∧ IsBoundedSubset (X := X) Y := by
  simpa using compactSubset_closed_and_bounded_prop (X := X) (Y := Y) hY

/-- Theorem 1.7 (Heine--Borel theorem): Let `n ∈ ℕ`, and let `d` be the Euclidean metric, the
taxicab metric, or the sup norm metric on `ℝ^n`. For a set `E ⊆ ℝ^n`, the following are
equivalent: (i) `E` is compact (every open cover admits a finite subcover). (ii) `E` is closed
and bounded. -/
theorem heineBorel_Rn_iff_isClosed_isBounded_prop (n : ℕ)
    (E : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact E ↔ IsClosed E ∧ Bornology.IsBounded E := by
  simpa using (Metric.isCompact_iff_isClosed_bounded (s := E))

/-- Heine--Borel on `ℝ^n`: compactness is equivalent to closedness and boundedness. -/
theorem heineBorel_Rn_iff_isClosed_isBounded (n : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact E ↔ IsClosed E ∧ Bornology.IsBounded E := by
  simpa using heineBorel_Rn_iff_isClosed_isBounded_prop n E

/-- Helper for Theorem 1.8: sequential compactness of a subset implies compactness. -/
lemma helperForTheorem_1_8_isCompact {X : Type*} [MetricSpace X] {Y : Set X}
    (hY : IsCompactSubset (X := X) Y) : IsCompact Y := by
  have hseq : IsCompact Y ↔ IsSeqCompact Y := by
    simpa using (UniformSpace.isCompact_iff_isSeqCompact (s := Y))
  exact hseq.mpr hY

/-- Theorem 1.8: Let `(X,d)` be a metric space, let `Y ⊆ X` be compact, and let `(V_α)_{α∈A}` be a
family of open subsets of `X` with `Y ⊆ ⋃ α, V α`. Then there exists a finite `F ⊆ A` such that
`Y ⊆ ⋃ α ∈ F, V α`. -/
theorem compactSubset_finite_subcover {X : Type*} [MetricSpace X] {Y : Set X}
    (hY : IsCompactSubset (X := X) Y) {A : Type*} (V : A → Set X)
    (hV : ∀ α, IsOpen (V α)) (hcover : Y ⊆ ⋃ α, V α) :
    ∃ F : Finset A, Y ⊆ ⋃ α ∈ F, V α := by
  have hcompact : IsCompact Y :=
    helperForTheorem_1_8_isCompact (X := X) (Y := Y) hY
  simpa using IsCompact.elim_finite_subcover hcompact V hV hcover

/-- Helper for Theorem 1.9: open-cover finite-subcover property implies compactness of `Set.univ`. -/
lemma helperForTheorem_1_9_isCompact_univ_of_openCover (Y : Type u) [TopologicalSpace Y]
    (hcover :
      ∀ {ι : Type u} (U : ι → Set Y), (∀ i, IsOpen (U i)) →
        (Set.univ ⊆ ⋃ i, U i) → ∃ s : Finset ι, Set.univ ⊆ ⋃ i ∈ s, U i) :
    IsCompact (Set.univ : Set Y) := by
  refine isCompact_of_finite_subcover (s := (Set.univ : Set Y)) ?_
  intro ι U hUopen hUcover
  exact hcover U hUopen hUcover

/-- Theorem 1.9 (Heine--Borel property implies compactness): Let `Y` be a topological space. If
every open cover of `Y` admits a finite subcover, then `Y` is compact. -/
theorem heineBorelProperty_implies_compactSpace (Y : Type u) [TopologicalSpace Y]
    (hcover :
      ∀ {ι : Type u} (U : ι → Set Y), (∀ i, IsOpen (U i)) →
        (Set.univ ⊆ ⋃ i, U i) → ∃ s : Finset ι, Set.univ ⊆ ⋃ i ∈ s, U i) :
    CompactSpace Y := by
  refine ⟨?_⟩
  exact helperForTheorem_1_9_isCompact_univ_of_openCover (Y := Y) hcover

/-- Theorem 1.10: Let `(K_n)_{n∈ℕ}` be a sequence of nonempty compact subsets of a metric space
`(X,d)` such that `K_{n+1} ⊆ K_n` for all `n`. Then `⋂ n, K n` is nonempty.
Nested nonempty compact sets have nonempty intersection. -/
theorem nested_compact_inter_nonempty {X : Type*} [MetricSpace X] (K : ℕ → Set X)
    (hKcompact : ∀ n, IsCompact (K n)) (hKnonempty : ∀ n, (K n).Nonempty)
    (hmono : ∀ n, K (n + 1) ⊆ K n) :
    (⋂ n, K n).Nonempty := by
  have hclosed : ∀ n, IsClosed (K n) := fun n => (hKcompact n).isClosed
  exact
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (t := K) hmono hKnonempty (hKcompact 0) hclosed

/-- Theorem 1.11: For a metric space `(X,d)` and a nested sequence of nonempty compact subsets
`K n` with `K (n+1) ⊆ K n`, the intersection `⋂_{n=1}^∞ K_n` is nonempty. -/
theorem nested_compact_inter_nonempty_from_one_prop {X : Type*} [MetricSpace X] (K : ℕ → Set X)
    (hKcompact : ∀ n, IsCompact (K n)) (hKnonempty : ∀ n, (K n).Nonempty)
    (hmono : ∀ n, K (n + 1) ⊆ K n) :
    (⋂ n, K (n + 1)).Nonempty := by
  simpa using
    (nested_compact_inter_nonempty (K := fun n => K (n + 1))
      (hKcompact := fun n => hKcompact (n + 1))
      (hKnonempty := fun n => hKnonempty (n + 1))
      (hmono := fun n => hmono (n + 1)))

/-- A nested sequence of nonempty compact subsets has nonempty intersection starting at `n = 1`. -/
theorem nested_compact_inter_nonempty_from_one {X : Type*} [MetricSpace X] (K : ℕ → Set X)
    (hKcompact : ∀ n, IsCompact (K n)) (hKnonempty : ∀ n, (K n).Nonempty)
    (hmono : ∀ n, K (n + 1) ⊆ K n) :
    (⋂ n, K (n + 1)).Nonempty :=
  nested_compact_inter_nonempty_from_one_prop (K := K) hKcompact hKnonempty hmono

/-- Helper for Theorem 1.12: compactness of `univ` in the subtype of a compact set. -/
lemma helperForTheorem_1_12_isCompact_univ_subtype {X : Type*} [MetricSpace X] {Y : Set X}
    (hY : IsCompact Y) : IsCompact (Set.univ : Set Y) := by
  have himage : IsCompact ((Subtype.val) '' (Set.univ : Set Y) : Set X) := by
    simpa [Set.image_univ, Subtype.range_coe] using hY
  exact (Subtype.isCompact_iff).2 himage

/-- Theorem 1.12: Let `(X,d)` be a metric space.
    (a) If `Y ⊆ X` is compact and `Z ⊆ Y`, then `Z` is compact iff `Z` is closed in `Y`.
    (b) If `Y₁, …, Yₙ ⊆ X` are compact, then `⋃ i, Yᵢ` is compact.
    (c) Every finite subset of `X` (including `∅`) is compact. -/
theorem compact_basic_properties (X : Type*) [MetricSpace X] :
    (∀ (Y : Set X), IsCompact Y → ∀ (Z : Set Y), IsCompact Z ↔ IsClosed Z) ∧
      (∀ {ι : Type*} (s : Finset ι) (Y : ι → Set X),
        (∀ i ∈ s, IsCompact (Y i)) → IsCompact (⋃ i ∈ s, Y i)) ∧
      (∀ {Z : Set X}, Z.Finite → IsCompact Z) := by
  constructor
  · intro Y hY Z
    constructor
    · intro hZ
      exact hZ.isClosed
    · intro hZclosed
      have hYuniv : IsCompact (Set.univ : Set Y) :=
        helperForTheorem_1_12_isCompact_univ_subtype (X := X) (Y := Y) hY
      exact IsCompact.of_isClosed_subset hYuniv hZclosed (Set.subset_univ _)
  · constructor
    · intro ι s Y hY
      exact s.isCompact_biUnion hY
    · intro Z hZ
      exact hZ.isCompact
/-- Theorem 1.12(a): In a compact subset `Y` of a metric space, `Z ⊆ Y` is compact iff it is
closed in `Y`. -/
theorem compact_subset_iff_closed_in_compact {X : Type*} [MetricSpace X] {Y : Set X}
    (hY : IsCompact Y) (Z : Set Y) :
    IsCompact Z ↔ IsClosed Z := by
  constructor
  · intro hZ
    exact hZ.isClosed
  · intro hZclosed
    have hYuniv : IsCompact (Set.univ : Set Y) :=
      helperForTheorem_1_12_isCompact_univ_subtype (X := X) (Y := Y) hY
    exact IsCompact.of_isClosed_subset hYuniv hZclosed (Set.subset_univ _)

/-- Theorem 1.12(b): A finite union of compact subsets is compact. -/
theorem compact_iUnion_finset {X : Type*} [MetricSpace X] {ι : Type*} (s : Finset ι)
    (Y : ι → Set X) (hY : ∀ i ∈ s, IsCompact (Y i)) :
    IsCompact (⋃ i ∈ s, Y i) := by
  exact s.isCompact_biUnion hY

/-- Theorem 1.12(c): Every finite subset of a metric space is compact. -/
theorem finite_isCompact {X : Type*} [MetricSpace X] {Z : Set X} (hZ : Z.Finite) :
    IsCompact Z := by
  exact hZ.isCompact

/-- Theorem 1.13 (Equivalence of sequential compactness and open cover compactness): Let `(X,d)`
be a metric space. The following are equivalent: (i) every sequence in `X` has a convergent
subsequence; (ii) every open cover of `X` has a finite subcover. -/
theorem sequentiallyCompactSpace_iff_compactOpenCoverSpace_prop (X : Type*) [MetricSpace X] :
    IsSequentiallyCompactSpace X ↔ IsCompactOpenCoverSpace X := by
  simpa [IsSequentiallyCompactSpace, IsCompactOpenCoverSpace] using
    (UniformSpace.compactSpace_iff_seqCompactSpace (X := X)).symm

/-- In a metric space, sequential compactness is equivalent to open-cover compactness. -/
theorem sequentiallyCompactSpace_iff_compactOpenCoverSpace (X : Type*) [MetricSpace X] :
    IsSequentiallyCompactSpace X ↔ IsCompactOpenCoverSpace X := by
  simpa using sequentiallyCompactSpace_iff_compactOpenCoverSpace_prop (X := X)

/-- Helper for Proposition 1.29: discrete distance on `ℤ`, `0` on the diagonal and `1` off it. -/
def intDiscreteDist (m n : ℤ) : ℝ :=
  if m = n then 0 else 1

/-- Helper for Proposition 1.29: the discrete distance on `ℤ` is zero on the diagonal. -/
lemma intDiscreteDist_self (m : ℤ) : intDiscreteDist m m = 0 := by
  simp [intDiscreteDist]

/-- Helper for Proposition 1.29: the discrete distance on `ℤ` is symmetric. -/
lemma intDiscreteDist_comm (m n : ℤ) : intDiscreteDist m n = intDiscreteDist n m := by
  by_cases h : m = n
  · subst h; simp [intDiscreteDist]
  · have h' : n ≠ m := by
      simpa [eq_comm] using h
    simp [intDiscreteDist, h, h']

/-- Helper for Proposition 1.29: the discrete distance on `ℤ` satisfies the triangle inequality. -/
lemma intDiscreteDist_triangle (m n k : ℤ) :
    intDiscreteDist m k ≤ intDiscreteDist m n + intDiscreteDist n k := by
  by_cases hmn : m = n
  · by_cases hnk : n = k
    · subst hmn; subst hnk; simp [intDiscreteDist]
    · subst hmn; simp [intDiscreteDist, hnk]
  · by_cases hnk : n = k
    · subst hnk; simp [intDiscreteDist, hmn]
    · by_cases hmk : m = k
      · subst hmk; simp [intDiscreteDist, hmn, hnk]
      · simp [intDiscreteDist, hmn, hnk, hmk]

/-- Helper for Proposition 1.29: zero discrete distance on `ℤ` implies equality. -/
lemma intDiscreteDist_eq_of_dist_eq_zero {m n : ℤ} :
    intDiscreteDist m n = 0 → m = n := by
  intro hdist
  by_cases h : m = n
  · exact h
  · exfalso
    have hne : intDiscreteDist m n ≠ 0 := by
      simp [intDiscreteDist, h]
    exact hne hdist

/-- Helper for Proposition 1.29: the metric space structure on `ℤ` induced by `intDiscreteDist`. -/
def intDiscreteMetricSpace : MetricSpace ℤ :=
  { dist := intDiscreteDist
    dist_self := intDiscreteDist_self
    dist_comm := intDiscreteDist_comm
    dist_triangle := intDiscreteDist_triangle
    eq_of_dist_eq_zero := intDiscreteDist_eq_of_dist_eq_zero }

section IntDiscreteMetricInstances

local instance : MetricSpace ℤ := intDiscreteMetricSpace
local instance : Dist ℤ := ⟨intDiscreteDist⟩
local instance : PseudoMetricSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace
local instance : UniformSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace
local instance : TopologicalSpace ℤ :=
  intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance : Bornology ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toBornology

/-- Helper for Proposition 1.29: in the discrete metric on `ℤ`, distance < 1/2 forces equality. -/
lemma helperForProposition_1_29_eq_of_dist_lt_one_half {m n : ℤ} :
    intDiscreteDist m n < (1 / 2 : ℝ) → m = n := by
  intro hlt
  by_cases h : m = n
  · exact h
  · exfalso
    have hlt' : (1 : ℝ) < (1 / 2 : ℝ) := by
      simpa [intDiscreteDist, h] using hlt
    have hge : (1 : ℝ) ≥ (1 / 2 : ℝ) := by
      norm_num
    exact (not_lt_of_ge hge hlt')

/-- Helper for Proposition 1.29: the discrete metric on `ℤ` induces the discrete topology. -/
lemma helperForProposition_1_29_discreteTopology_intDiscrete :
    letI : MetricSpace ℤ := intDiscreteMetricSpace
    letI : Dist ℤ := ⟨intDiscreteDist⟩
    letI : UniformSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace
    letI : TopologicalSpace ℤ :=
      intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    DiscreteTopology ℤ := by
  letI : MetricSpace ℤ := intDiscreteMetricSpace
  letI : Dist ℤ := ⟨intDiscreteDist⟩
  letI : PseudoMetricSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace
  letI : UniformSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace ℤ :=
    intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hpos : (0 : ℝ) < (1 : ℝ) := by
    norm_num
  refine DiscreteTopology.of_forall_le_dist (α := ℤ) (r := (1 : ℝ)) hpos ?_
  intro m n hne
  change (1 : ℝ) ≤ intDiscreteDist m n
  simp [intDiscreteDist, hne]

/-- Helper for Proposition 1.29: completeness of the discrete metric on `ℤ`. -/
lemma helperForProposition_1_29_completeSpace_intDiscrete :
    letI : MetricSpace ℤ := intDiscreteMetricSpace
    letI : Dist ℤ := ⟨intDiscreteDist⟩
    letI : UniformSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace
    CompleteSpace ℤ := by
  letI : MetricSpace ℤ := intDiscreteMetricSpace
  letI : Dist ℤ := ⟨intDiscreteDist⟩
  letI : PseudoMetricSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace
  letI : UniformSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace
  refine Metric.complete_of_cauchySeq_tendsto (α := ℤ) ?_
  intro u hu
  have hC : ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N, dist (u n) (u N) < ε :=
    (Metric.cauchySeq_iff' (α := ℤ) (u := u)).1 hu
  obtain ⟨N, hN⟩ := hC (1 / 2) (by norm_num)
  refine ⟨u N, ?_⟩
  have hconst : ∀ n ≥ N, u n = u N := by
    intro n hn
    have hdist : dist (u n) (u N) < (1 / 2 : ℝ) := hN n hn
    have hdist' : intDiscreteDist (u n) (u N) < (1 / 2 : ℝ) := by
      simpa [intDiscreteDist] using hdist
    exact helperForProposition_1_29_eq_of_dist_lt_one_half hdist'
  exact tendsto_atTop_of_eventually_const (i₀ := N) hconst

/-- Helper for Proposition 1.29: boundedness of the discrete metric on `ℤ`. -/
lemma helperForProposition_1_29_boundedSpace_intDiscrete :
    letI : MetricSpace ℤ := intDiscreteMetricSpace
    letI : Dist ℤ := ⟨intDiscreteDist⟩
    letI : Bornology ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toBornology
    BoundedSpace ℤ := by
  letI : MetricSpace ℤ := intDiscreteMetricSpace
  letI : Dist ℤ := ⟨intDiscreteDist⟩
  letI : PseudoMetricSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace
  letI : Bornology ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toBornology
  refine (Metric.boundedSpace_iff (α := ℤ)).2 ?_
  refine ⟨1, ?_⟩
  intro a b
  by_cases h : a = b
  · change intDiscreteDist a b ≤ 1
    simp [intDiscreteDist, h]
  · change intDiscreteDist a b ≤ 1
    simp [intDiscreteDist, h]

/-- Helper for Proposition 1.29: `ℤ` with the discrete metric is not compact. -/
lemma helperForProposition_1_29_not_compactSpace_intDiscrete :
    letI : MetricSpace ℤ := intDiscreteMetricSpace
    letI : Dist ℤ := ⟨intDiscreteDist⟩
    letI : UniformSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace
    letI : TopologicalSpace ℤ :=
      intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    ¬ CompactSpace ℤ := by
  letI : MetricSpace ℤ := intDiscreteMetricSpace
  letI : Dist ℤ := ⟨intDiscreteDist⟩
  letI : UniformSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace ℤ :=
    intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  haveI : DiscreteTopology ℤ := helperForProposition_1_29_discreteTopology_intDiscrete
  intro hcompact
  haveI : CompactSpace ℤ := hcompact
  have hcompact_univ : IsCompact (Set.univ : Set ℤ) := isCompact_univ
  have hfinite : (Set.univ : Set ℤ).Finite := (isCompact_iff_finite).1 hcompact_univ
  exact (Set.infinite_univ : (Set.univ : Set ℤ).Infinite) hfinite

/-- Proposition 1.29: Let `(X,d)` be a metric space and equip `ℤ` with the discrete metric
`d(m,n)=1` when `m ≠ n` (and `0` otherwise). Then `ℤ` is complete and bounded, but not compact. -/
theorem int_discreteMetric_complete_bounded_not_compact :
    letI : MetricSpace ℤ := intDiscreteMetricSpace
    CompleteSpace ℤ ∧ BoundedSpace ℤ ∧ ¬ CompactSpace ℤ := by
  letI : MetricSpace ℤ := intDiscreteMetricSpace
  letI : Dist ℤ := ⟨intDiscreteDist⟩
  have hcomplete : CompleteSpace ℤ := by
    simpa using helperForProposition_1_29_completeSpace_intDiscrete
  have hbounded : BoundedSpace ℤ := by
    simpa using helperForProposition_1_29_boundedSpace_intDiscrete
  have hnotcompact : ¬ CompactSpace ℤ := by
    simpa using helperForProposition_1_29_not_compactSpace_intDiscrete
  exact ⟨hcomplete, hbounded, hnotcompact⟩

end IntDiscreteMetricInstances

/-- Helper for Proposition 1.36: every integer lies in the ball of radius `2` around `0`. -/
lemma helperForProposition_1_36_mem_ball_zero_two_intDiscrete (z : ℤ) :
    letI : MetricSpace ℤ := intDiscreteMetricSpace
    letI : Dist ℤ := ⟨intDiscreteDist⟩
    letI : PseudoMetricSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace
    z ∈ Metric.ball (0 : ℤ) 2 := by
  letI : MetricSpace ℤ := intDiscreteMetricSpace
  letI : Dist ℤ := ⟨intDiscreteDist⟩
  letI : PseudoMetricSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace
  change dist z (0 : ℤ) < (2 : ℝ)
  change intDiscreteDist z 0 < (2 : ℝ)
  by_cases h : z = 0
  · subst h
    have h02 : (0 : ℝ) < 2 := by
      norm_num
    simpa [intDiscreteDist] using h02
  · have h12 : (1 : ℝ) < 2 := by
      norm_num
    simpa [intDiscreteDist, h] using h12

/-- Helper for Proposition 1.36: `univ` is bounded for the discrete metric on `ℤ`. -/
lemma helperForProposition_1_36_isBoundedSubset_univ_intDiscrete :
    letI : MetricSpace ℤ := intDiscreteMetricSpace
    letI : Dist ℤ := ⟨intDiscreteDist⟩
    letI : PseudoMetricSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace
    IsBoundedSubset (X:=ℤ) (Set.univ : Set ℤ) := by
  letI : MetricSpace ℤ := intDiscreteMetricSpace
  letI : Dist ℤ := ⟨intDiscreteDist⟩
  letI : PseudoMetricSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace
  refine Or.inr ?_
  refine ⟨(0 : ℤ), (2 : ℝ), ?_, ?_⟩
  · norm_num
  · intro z _
    exact helperForProposition_1_36_mem_ball_zero_two_intDiscrete z

/-- Helper for Proposition 1.36: `univ` is not compact in the discrete metric on `ℤ`. -/
lemma helperForProposition_1_36_not_isCompact_univ_intDiscrete :
    letI : MetricSpace ℤ := intDiscreteMetricSpace
    letI : Dist ℤ := ⟨intDiscreteDist⟩
    letI : UniformSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace
    letI : TopologicalSpace ℤ :=
      intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    ¬ IsCompact (Set.univ : Set ℤ) := by
  letI : MetricSpace ℤ := intDiscreteMetricSpace
  letI : Dist ℤ := ⟨intDiscreteDist⟩
  letI : UniformSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace ℤ :=
    intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  haveI : DiscreteTopology ℤ := helperForProposition_1_29_discreteTopology_intDiscrete
  intro hcompact
  have hfinite : (Set.univ : Set ℤ).Finite := (isCompact_iff_finite).1 hcompact
  exact (Set.infinite_univ : (Set.univ : Set ℤ).Infinite) hfinite

/-- Proposition 1.36: [Heine-Borel fails for discrete metric on `ℤ`]
In the discrete metric on `ℤ`, the set `ℤ` is closed and bounded, but not compact.
In the discrete metric on `ℤ`, the whole space is closed and bounded but not compact. -/
theorem int_discrete_closed_bounded_not_compact :
    letI : MetricSpace ℤ := intDiscreteMetricSpace
    IsClosed (Set.univ : Set ℤ) ∧ IsBoundedSubset (X:=ℤ) (Set.univ) ∧
      ¬ IsCompactOpenCover (X:=ℤ) (Set.univ) := by
  letI : MetricSpace ℤ := intDiscreteMetricSpace
  refine ⟨?_, ?_, ?_⟩
  · exact isClosed_univ
  · exact helperForProposition_1_36_isBoundedSubset_univ_intDiscrete
  · letI : Dist ℤ := ⟨intDiscreteDist⟩
    letI : UniformSpace ℤ := intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace
    letI : TopologicalSpace ℤ :=
      intDiscreteMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    have hnotcompact : ¬ IsCompact (Set.univ : Set ℤ) :=
      helperForProposition_1_36_not_isCompact_univ_intDiscrete
    simpa [IsCompactOpenCover] using hnotcompact

end Section05
end Chap01
