import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_2.Problem

open scoped Matrix MixedIntegerNotation

section Definition13

variable {m n p : ℕ}

/-- Definition 1.3 (1): the mixed `0,1` linear set
`{(x, y) ∈ {0,1}^n × ℝ_+^p | A *ᵥ x + G *ᵥ y ≤ b}` attached to real data `A`, `G`, and `b`. -/
def mixedZeroOneLinearSet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    Set (MixedRealPoint n p) :=
  lp_relaxation_feasible_set A G b ∩
    {xy | ∀ i : Fin n, xy.1 i = 0 ∨ xy.1 i = 1}

namespace mixedZeroOneLinearSet

/-- `mixedZeroOneLinearSet A G b` is the binary slice of the Chapter 1 LP-relaxation feasible
region. -/
theorem eq_inter_lpRelaxation
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    mixedZeroOneLinearSet A G b =
      lp_relaxation_feasible_set A G b ∩
        {xy | ∀ i : Fin n, xy.1 i = 0 ∨ xy.1 i = 1} :=
  rfl

end mixedZeroOneLinearSet

/-- Membership in `mixedZeroOneLinearSet A G b` is exactly the source system
`A *ᵥ x + G *ᵥ y ≤ b`, binary `x`, and nonnegative `y`. -/
theorem mem_mixedZeroOneLinearSet_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (xy : MixedRealPoint n p) :
    xy ∈ mixedZeroOneLinearSet A G b ↔
      A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧
        (∀ i : Fin n, xy.1 i = 0 ∨ xy.1 i = 1) ∧
        0 ≤ xy.2 := by
  rw [mixedZeroOneLinearSet, Set.mem_inter_iff, mem_lp_relaxation_feasible_set_iff]
  constructor
  · rintro ⟨⟨hineq, -, hy_nonneg⟩, hx_binary⟩
    exact ⟨hineq, hx_binary, hy_nonneg⟩
  · rintro ⟨hineq, hx_binary, hy_nonneg⟩
    refine ⟨?_, hx_binary⟩
    refine ⟨hineq, ?_, hy_nonneg⟩
    intro i
    rcases hx_binary i with hxi | hxi
    · simp [hxi]
    · simp [hxi]

namespace MixedIntegerLinearProgram

/-- The mixed `0,1` linear set cut out by the coefficient data of `P`. -/
def mixedZeroOneFeasibleSet (P : MixedIntegerLinearProgram m n p) : Set (MixedRealPoint n p) :=
  mixedZeroOneLinearSet P.integerMatrix P.continuousMatrix P.rhs

/-- `P.mixedZeroOneFeasibleSet` is the canonical mixed `0,1` feasible set attached to the
coefficient data of `P`. -/
theorem mixedZeroOneFeasibleSet_eq_mixedZeroOneLinearSet
    (P : MixedIntegerLinearProgram m n p) :
    P.mixedZeroOneFeasibleSet =
      mixedZeroOneLinearSet P.integerMatrix P.continuousMatrix P.rhs :=
  rfl

/-- Membership in `P.mixedZeroOneFeasibleSet` is exactly the source system `A *ᵥ x + G *ᵥ y ≤ b`
together with binary `x` and nonnegative `y`. -/
theorem mem_mixedZeroOneFeasibleSet_iff
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) :
    xy ∈ P.mixedZeroOneFeasibleSet ↔
      P.integerMatrix *ᵥ xy.1 + P.continuousMatrix *ᵥ xy.2 ≤ P.rhs ∧
        (∀ i : Fin n, xy.1 i = 0 ∨ xy.1 i = 1) ∧
        0 ≤ xy.2 := by
  simpa [mixedZeroOneFeasibleSet] using
    mem_mixedZeroOneLinearSet_iff P.integerMatrix P.continuousMatrix P.rhs xy

/-- Every mixed `0,1` feasible point of `P` is feasible for the underlying mixed integer linear
program; binary first-block coordinates are automatically nonnegative integers. -/
theorem mixedZeroOneFeasibleSet_subset_feasibleSet
    (P : MixedIntegerLinearProgram m n p) :
    P.mixedZeroOneFeasibleSet ⊆ P.feasibleSet := by
  intro xy hxy
  rw [P.mem_feasibleSet_iff_mem_mixed_integer_lattice]
  rw [P.mem_mixedZeroOneFeasibleSet_iff] at hxy
  rcases hxy with ⟨hineq, hx_binary, hy_nonneg⟩
  have hx_nonneg : 0 ≤ xy.1 := by
    intro i
    rcases hx_binary i with hxi | hxi
    · simp [hxi]
    · simp [hxi]
  refine ⟨hineq, hx_nonneg, hy_nonneg, ?_⟩
  rw [mem_mixed_integer_lattice_exists_iff]
  refine ⟨fun i ↦ if xy.1 i = 0 then 0 else 1, ?_⟩
  funext i
  rcases hx_binary i with hxi | hxi
  · simp [hxi]
  · simp [hxi]

/-- Definition 1.3 (2): a mixed `0,1` linear program is a mixed integer linear program whose
feasible set is the mixed `0,1` linear set determined by its coefficient data. -/
def IsMixedZeroOne (P : MixedIntegerLinearProgram m n p) : Prop :=
  P.feasibleSet = P.mixedZeroOneFeasibleSet

/-- `P` is mixed `0,1` exactly when feasible membership is equivalent to the defining mixed
`0,1` system cut out by its coefficient data. -/
theorem isMixedZeroOne_iff
    (P : MixedIntegerLinearProgram m n p) :
    P.IsMixedZeroOne ↔
      ∀ xy : MixedRealPoint n p,
        xy ∈ P.feasibleSet ↔
          P.integerMatrix *ᵥ xy.1 + P.continuousMatrix *ᵥ xy.2 ≤ P.rhs ∧
            (∀ i : Fin n, xy.1 i = 0 ∨ xy.1 i = 1) ∧
            0 ≤ xy.2 := by
  constructor
  · intro hP xy
    rw [hP]
    exact P.mem_mixedZeroOneFeasibleSet_iff xy
  · intro hP
    ext xy
    rw [P.mem_mixedZeroOneFeasibleSet_iff]
    exact hP xy

/-- Since every mixed `0,1` feasible point is already MILP-feasible, `P` is mixed `0,1` exactly
when every feasible point of `P` lies in the canonical mixed `0,1` feasible set. -/
theorem isMixedZeroOne_iff_feasibleSet_subset_mixedZeroOneFeasibleSet
    (P : MixedIntegerLinearProgram m n p) :
    P.IsMixedZeroOne ↔ P.feasibleSet ⊆ P.mixedZeroOneFeasibleSet := by
  constructor
  · intro hP
    rw [hP]
  · intro hP
    exact Set.Subset.antisymm hP P.mixedZeroOneFeasibleSet_subset_feasibleSet

end MixedIntegerLinearProgram

end Definition13
