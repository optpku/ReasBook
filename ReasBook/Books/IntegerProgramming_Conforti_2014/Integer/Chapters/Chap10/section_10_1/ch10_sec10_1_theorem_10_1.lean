import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix MatrixOrder

-- Domain sampling for this theorem:
-- * primary domain: semidefinite programming over real symmetric matrices
-- * project owner surface inspected: Chapter 3
--   `primal_feasible_region`, `dual_feasible_region`,
--   `primal_objective_values`, `dual_objective_values`
-- * core/canonical owners reused directly: `Matrix.PosSemidef`, `Matrix.PosDef`,
--   `Matrix.PosDef.posSemidef`, `Matrix.PosSemidef.submatrix`
-- * source-facing owners kept here: `sdp_dual_slack`, `sdp_primal_feasible_region`,
--   `sdp_dual_feasible_region`, `sdp_primal_objective`, `sdp_dual_objective`,
--   `sdp_primal_objective_values`, `sdp_dual_objective_values`

section Theorem101

variable {m n : ℕ}

noncomputable instance instNormedAddCommGroupRealMatrix :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := by
  exact Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

noncomputable instance instInnerProductSpaceRealMatrix :
    InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  exact Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

noncomputable instance instNormedSpaceRealMatrix :
    NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  letI : InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := instInnerProductSpaceRealMatrix
  infer_instance

/-- The primal feasible region consists of positive semidefinite matrices satisfying the equality
constraints `Tr (Aᵢ X) = bᵢ`. -/
def sdp_primal_feasible_region
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.PosSemidef ∧ ∀ i, Matrix.trace (A i * X) = b i}

/-- Membership in `sdp_primal_feasible_region A b` means positive semidefiniteness together with
the trace constraints `Tr (Aᵢ X) = bᵢ`. -/
theorem mem_sdp_primal_feasible_region_iff
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    X ∈ sdp_primal_feasible_region A b ↔
      X.PosSemidef ∧ ∀ i, Matrix.trace (A i * X) = b i := Iff.rfl

/-- The dual slack matrix `∑ᵢ yᵢ Aᵢ - C` associated to a dual vector `y`. -/
def sdp_dual_slack
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (∑ i, y i • A i) - C

/-- The dual feasible region consists of vectors whose slack matrix `∑ᵢ yᵢ Aᵢ - C` is positive
semidefinite. -/
def sdp_dual_feasible_region
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Set (Fin m → ℝ) :=
  {y | (sdp_dual_slack A C y).PosSemidef}

/-- Membership in `sdp_dual_feasible_region A C` means positive semidefiniteness of the dual
slack matrix. -/
theorem mem_sdp_dual_feasible_region_iff
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin m → ℝ) :
    y ∈ sdp_dual_feasible_region A C ↔ (sdp_dual_slack A C y).PosSemidef := Iff.rfl

/-- The primal objective values attained on the primal feasible region. -/
def sdp_primal_objective
    (C : Matrix (Fin n) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (C * X)

/-- The dual objective `∑ᵢ yᵢ bᵢ` attached to the right-hand side `b`. -/
def sdp_dual_objective
    (b : Fin m → ℝ) (y : Fin m → ℝ) : ℝ :=
  ∑ i, y i * b i

/-- The primal objective values attained on the primal feasible region. -/
def sdp_primal_objective_values
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  sdp_primal_objective C '' sdp_primal_feasible_region A b

/-- Membership in `sdp_primal_objective_values A b C` means that some primal-feasible matrix
attains the value `r`. -/
theorem mem_sdp_primal_objective_values_iff
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    r ∈ sdp_primal_objective_values A b C ↔
      ∃ X : Matrix (Fin n) (Fin n) ℝ,
        X ∈ sdp_primal_feasible_region A b ∧ sdp_primal_objective C X = r := Iff.rfl

/-- The dual objective values attained by vectors whose slack matrix `∑ᵢ yᵢ Aᵢ - C` is positive
semidefinite. -/
def sdp_dual_objective_values
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  sdp_dual_objective b '' sdp_dual_feasible_region A C

/-- Membership in `sdp_dual_objective_values A b C` means that some dual-feasible vector attains
the value `r`. -/
theorem mem_sdp_dual_objective_values_iff
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    r ∈ sdp_dual_objective_values A b C ↔
      ∃ y : Fin m → ℝ,
        y ∈ sdp_dual_feasible_region A C ∧ sdp_dual_objective b y = r := Iff.rfl

/-- The primal problem is strictly feasible when one feasible matrix is positive definite. -/
def sdp_primal_strictly_feasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∃ X : Matrix (Fin n) (Fin n) ℝ, X.PosDef ∧ ∀ i, Matrix.trace (A i * X) = b i

/-- The dual problem is strictly feasible when one dual slack matrix is positive definite. -/
def sdp_dual_strictly_feasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ y : Fin m → ℝ, (sdp_dual_slack A C y).PosDef

namespace sdp_primal_strictly_feasible

/-- A strictly feasible primal witness is, in particular, a primal-feasible matrix. -/
theorem exists_mem_primal_feasible_region
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (h : sdp_primal_strictly_feasible A b) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X ∈ sdp_primal_feasible_region A b ∧ X.PosDef := by
  rcases h with ⟨X, hX, hAX⟩
  exact ⟨X, ⟨hX.posSemidef, hAX⟩, hX⟩

end sdp_primal_strictly_feasible

namespace sdp_dual_strictly_feasible

/-- A strictly feasible dual witness is, in particular, dual feasible. -/
theorem exists_mem_dual_feasible_region
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (h : sdp_dual_strictly_feasible A C) :
    ∃ y : Fin m → ℝ,
      y ∈ sdp_dual_feasible_region A C ∧ (sdp_dual_slack A C y).PosDef := by
  rcases h with ⟨y, hy⟩
  exact ⟨y, hy.posSemidef, hy⟩

end sdp_dual_strictly_feasible

/-- Helper for Theorem 10.1: the trace pairing of two positive semidefinite real matrices is
nonnegative. -/
lemma psdTraceMulNonneg
    {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ Matrix.trace (X * Y) := by
  classical
  -- Rewrite one PSD factor as `Zᴴ * Z` so the remaining trace is visibly nonnegative.
  obtain ⟨Z, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  have htrace : 0 ≤ Matrix.trace (Z * X * Zᴴ) :=
    (hX.mul_mul_conjTranspose_same Z).trace_nonneg
  -- Cycle the trace back to the original product.
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm] at htrace
  simpa [Matrix.mul_assoc] using htrace

/-- Helper for Theorem 10.1: any primal-feasible matrix and dual-feasible vector satisfy the SDP
weak-duality inequality. -/
lemma sdpWeakDualityFeasiblePair
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    {X : Matrix (Fin n) (Fin n) ℝ} {y : Fin m → ℝ}
    (hX : X ∈ sdp_primal_feasible_region A b)
    (hy : y ∈ sdp_dual_feasible_region A C) :
    sdp_primal_objective C X ≤ sdp_dual_objective b y := by
  rcases hX with ⟨hXpsd, hprimal⟩
  have hdual : (sdp_dual_slack A C y).PosSemidef := hy
  have hdualTrace :
      Matrix.trace ((∑ i, y i • A i) * X) = sdp_dual_objective b y := by
    -- Expand the trace term and substitute the primal trace constraints.
    calc
      Matrix.trace ((∑ i, y i • A i) * X)
          = Matrix.trace (∑ i, (y i • A i) * X) := by
              rw [Finset.sum_mul]
      _ = ∑ i, Matrix.trace ((y i • A i) * X) := by
            rw [Matrix.trace_sum]
      _ = ∑ i, y i * Matrix.trace (A i * X) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [smul_mul_assoc, Matrix.trace_smul]
            ring
      _ = ∑ i, y i * b i := by
            simp [hprimal]
      _ = sdp_dual_objective b y := rfl
  have hslackTrace :
      Matrix.trace ((sdp_dual_slack A C y) * X) =
        sdp_dual_objective b y - sdp_primal_objective C X := by
    -- Rewrite the slack matrix as `(∑ i, y i • A i) - C` and separate the trace.
    calc
      Matrix.trace ((sdp_dual_slack A C y) * X)
          = Matrix.trace ((((∑ i, y i • A i) - C) * X)) := by
              rfl
      _ = Matrix.trace (((∑ i, y i • A i) * X) - C * X) := by
            rw [sub_mul]
      _ = Matrix.trace (((∑ i, y i • A i) * X)) - Matrix.trace (C * X) := by
            rw [Matrix.trace_sub]
      _ = sdp_dual_objective b y - sdp_primal_objective C X := by
            rw [hdualTrace, sdp_primal_objective]
  have hnonneg : 0 ≤ Matrix.trace ((sdp_dual_slack A C y) * X) :=
    psdTraceMulNonneg hdual hXpsd
  -- The trace of the slack product is the duality gap.
  have hgap : 0 ≤ sdp_dual_objective b y - sdp_primal_objective C X := by
    simpa [hslackTrace] using hnonneg
  exact sub_nonneg.mp hgap

/-- Helper for Theorem 10.1: the dual slack matrix stays symmetric when the SDP data are
symmetric. -/
lemma sdpDualSlack_isSymm
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) (y : Fin m → ℝ) :
    (sdp_dual_slack A C y).IsSymm := by
  -- Symmetry is preserved by the finite linear combination defining the slack matrix.
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  calc
    (sdp_dual_slack A C y) j i = ((∑ k, y k • A k) - C) j i := by
      rfl
    _ = (∑ k, y k * A k j i) - C j i := by
      simp [Matrix.sub_apply, Matrix.sum_apply]
    _ = (∑ k, y k * A k i j) - C i j := by
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro k hk
        rw [(hA k).apply i j]
      · rw [hC.apply i j]
    _ = ((∑ k, y k • A k) - C) i j := by
      simp [Matrix.sub_apply, Matrix.sum_apply]
    _ = (sdp_dual_slack A C y) i j := by
      rfl

/-- Helper for Theorem 10.1: symmetric matrices form a linear subspace of the ambient matrix
space, so we package them as a submodule to inherit the canonical additive and topological API. -/
def symmSubmodule (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {X | X.IsSymm}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simpa using hX.add hY
  smul_mem' := by
    intro r X hX
    simpa using hX.smul r

/-- Helper for Theorem 10.1: the symmetric-matrix ambient space used for cone separation. -/
abbrev SymmMat (n : ℕ) : Type := ↥(symmSubmodule n)

instance instAddCommGroupSymmMat : AddCommGroup (SymmMat n) :=
  inferInstanceAs (AddCommGroup ↥(symmSubmodule n))

instance instModuleSymmMat : Module ℝ (SymmMat n) :=
  inferInstanceAs (Module ℝ ↥(symmSubmodule n))

noncomputable instance instNormedAddCommGroupSymmMat : NormedAddCommGroup (SymmMat n) := by
  exact Submodule.normedAddCommGroup (symmSubmodule n)

noncomputable instance instPseudoMetricSpaceSymmMat : PseudoMetricSpace (SymmMat n) :=
  instNormedAddCommGroupSymmMat.toPseudoMetricSpace

noncomputable instance instTopologicalSpaceSymmMat : TopologicalSpace (SymmMat n) :=
  instPseudoMetricSpaceSymmMat.toUniformSpace.toTopologicalSpace

noncomputable instance instNormedSpaceSymmMat : NormedSpace ℝ (SymmMat n) := by
  infer_instance

/-- Helper for Theorem 10.1: the symmetric ambient space inherits the Frobenius inner product from
the ambient matrix space, which is the inner-product structure used by the cone-separation API. -/
noncomputable instance instInnerProductSpaceSymmMat : InnerProductSpace ℝ (SymmMat n) := by
  infer_instance

/-- Helper for Theorem 10.1: the symmetric ambient space is complete, so `ProperCone` separation
theorems apply once the cone packaging is normalized. -/
noncomputable instance instCompleteSpaceSymmMat : CompleteSpace (SymmMat n) := by
  exact FiniteDimensional.complete ℝ (SymmMat n)

/-- Helper for Theorem 10.1: the rank-one matrix `u uᵀ` is symmetric. -/
lemma isSymm_vecMulVec_self (u : Fin n → ℝ) :
    (Matrix.vecMulVec u u).IsSymm := by
  -- Each entry is `u i * u j`, so commutativity swaps the indices.
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- Helper for Theorem 10.1: the canonical symmetric rank-one generator `u uᵀ`. -/
def rankOneSymmGenerator (u : Fin n → ℝ) : SymmMat n :=
  ⟨Matrix.vecMulVec u u, isSymm_vecMulVec_self u⟩

/-- Helper for Theorem 10.1: multiplying by the rank-one matrix `u uᵀ` and taking the trace
recovers the quadratic form `uᵀ X u`. -/
lemma trace_mul_rankOneSymmGenerator_eq_dotProduct_mulVec
    (u : Fin n → ℝ) (X : SymmMat n) :
    Matrix.trace (X.1 * Matrix.vecMulVec u u) = u ⬝ᵥ (X.1 *ᵥ u) := by
  -- Push the rank-one factor through the matrix product so `trace_vecMulVec` applies directly.
  calc
    Matrix.trace (X.1 * Matrix.vecMulVec u u)
        = Matrix.trace (Matrix.vecMulVec (X.1 *ᵥ u) u) := by
            rw [Matrix.mul_vecMulVec]
    _ = (X.1 *ᵥ u) ⬝ᵥ u := by
          rw [Matrix.trace_vecMulVec]
    _ = u ⬝ᵥ (X.1 *ᵥ u) := by
          rw [dotProduct_comm]

/-- Helper for Theorem 10.1: the inherited Frobenius inner product on `SymmMat n` evaluates
against a rank-one generator as the corresponding quadratic form. -/
lemma rankOneSymmGenerator_inner_eq_dotProduct_mulVec
    (u : Fin n → ℝ) (X : SymmMat n) :
    inner ℝ (rankOneSymmGenerator u) X = u ⬝ᵥ (X.1 *ᵥ u) := by
  -- Move from the subtype inner product to the ambient matrix pairing, then collapse the
  -- Frobenius trace formula against the symmetric rank-one matrix.
  rw [Submodule.coe_inner]
  calc
    Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ) * 1 * (Matrix.vecMulVec u u)ᴴ)
        = Matrix.trace (X.1 * Matrix.vecMulVec u u) := by
            rw [Matrix.mul_one, Matrix.conjTranspose_vecMulVec]
            simp
    _ = u ⬝ᵥ (X.1 *ᵥ u) := trace_mul_rankOneSymmGenerator_eq_dotProduct_mulVec u X

/-- Helper for Theorem 10.1: the PSD cone on symmetric matrices packaged as the inner dual of the
rank-one generators. -/
noncomputable def symmPsdProperCone (n : ℕ) :
    @ProperCone ℝ (SymmMat n) Real.semiring Real.partialOrder Real.instIsOrderedRing
      instNormedAddCommGroupSymmMat.toAddCommMonoid
      instNormedAddCommGroupSymmMat.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      instInnerProductSpaceSymmMat.toModule :=
  ProperCone.innerDual (Set.range rankOneSymmGenerator)

/-- Helper for Theorem 10.1: membership in the symmetric inner-dual cone is exactly positive
semidefiniteness of the underlying symmetric matrix. -/
lemma mem_symmPsdProperCone_iff
    (X : SymmMat n) :
    X ∈ symmPsdProperCone n ↔ X.1.PosSemidef := by
  constructor
  · intro hX
    -- Rewrite inner-dual membership into quadratic-form nonnegativity on all rank-one generators.
    have hsymm : X.1.IsSymm := X.2
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.IsHermitian.ext fun i j => by simpa using hsymm.apply i j
    · intro u
      have hmem : rankOneSymmGenerator u ∈ (Set.range rankOneSymmGenerator : Set (SymmMat n)) :=
        ⟨u, rfl⟩
      have hu :
          0 ≤ inner ℝ (rankOneSymmGenerator u) X := by
        exact (ProperCone.mem_innerDual.mp (by simpa [symmPsdProperCone] using hX)) hmem
      rw [rankOneSymmGenerator_inner_eq_dotProduct_mulVec] at hu
      exact hu
  · intro hX
    -- Positive semidefiniteness gives nonnegative pairing with each rank-one generator.
    rw [symmPsdProperCone, ProperCone.mem_innerDual]
    intro Y hY
    rcases hY with ⟨u, rfl⟩
    rw [rankOneSymmGenerator_inner_eq_dotProduct_mulVec]
    exact hX.dotProduct_mulVec_nonneg u

/-- Helper for Theorem 10.1: the homogenized domain cone combines symmetric PSD matrices with a
nonnegative scalar coordinate. -/
noncomputable def symmPsdScalarProperCone (n : ℕ) : ProperCone ℝ (SymmMat n × ℝ) :=
  { toSubmodule :=
      { carrier := {p | p.1.1.PosSemidef ∧ 0 ≤ p.2}
        zero_mem' := by
          constructor
          · simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
          · simp
        add_mem' := by
          intro x y hx hy
          constructor
          · exact hx.1.add hy.1
          · simpa using add_nonneg hx.2 hy.2
        smul_mem' := by
          intro a x hx
          constructor
          · exact hx.1.smul a.2
          · simpa [smul_eq_mul] using mul_nonneg a.2 hx.2 }
    isClosed' := by
      have hMatrix : IsClosed {X : SymmMat n | X.1.PosSemidef} := by
        -- The symmetric PSD cone is already closed; this line just rewrites its carrier set.
        have hEq : ({X : SymmMat n | X.1.PosSemidef} : Set (SymmMat n)) = symmPsdProperCone n := by
          ext X
          exact (mem_symmPsdProperCone_iff X).symm
        rw [hEq]
        exact (symmPsdProperCone n).isClosed
      have hScalar : IsClosed {τ : ℝ | 0 ≤ τ} := isClosed_Ici
      simpa [Set.preimage, Set.setOf_and]
        using (hMatrix.preimage continuous_fst).inter (hScalar.preimage continuous_snd) }

/-- Helper for Theorem 10.1: membership in the homogenized cone is exactly PSD together with a
nonnegative scale. -/
lemma mem_symmPsdScalarProperCone_iff
    (X : SymmMat n) (τ : ℝ) :
    (X, τ) ∈ symmPsdScalarProperCone n ↔ X.1.PosSemidef ∧ 0 ≤ τ := by
  -- The product-cone packaging is only a thin wrapper around the two component memberships.
  rfl

/-- Helper for Theorem 10.1: the inherited Frobenius inner product on `SymmMat n` is the trace
pairing of the underlying symmetric matrices. -/
lemma inner_symmMat_eq_trace_mul
    (X Y : SymmMat n) :
    inner ℝ X Y = Matrix.trace (Y.1 * X.1) := by
  -- Rewrite the subtype inner product back to the ambient Frobenius pairing.
  have hconj : ((X : Matrix (Fin n) (Fin n) ℝ)ᴴ) = X.1 := by
    ext i j
    simpa using (X.2.apply j i).symm
  rw [Submodule.coe_inner]
  calc
    Matrix.trace ((Y : Matrix (Fin n) (Fin n) ℝ) * 1 * (X : Matrix (Fin n) (Fin n) ℝ)ᴴ)
        = Matrix.trace (Y.1 * X.1) := by
            rw [Matrix.mul_one, hconj]

/-- Helper for Theorem 10.1: two symmetric PSD matrices have nonnegative Frobenius pairing. -/
lemma inner_symmMat_nonneg_of_posSemidef
    {X Y : SymmMat n} (hX : X.1.PosSemidef) (hY : Y.1.PosSemidef) :
    0 ≤ inner ℝ X Y := by
  -- Reduce the subtype inner product to the ambient trace pairing and reuse the PSD trace lemma.
  rw [inner_symmMat_eq_trace_mul]
  exact psdTraceMulNonneg hY hX

/-- Helper for Theorem 10.1: each symmetric rank-one generator lies in the PSD cone. -/
lemma rankOneSymmGenerator_mem_symmPsdProperCone
    (u : Fin n → ℝ) :
    rankOneSymmGenerator u ∈ symmPsdProperCone n := by
  -- The rank-one generator is PSD because it is `u uᵀ`.
  rw [mem_symmPsdProperCone_iff]
  simpa using Matrix.posSemidef_vecMulVec_self_star u

/-- Helper for Theorem 10.1: the homogenized PSD-and-scale cone on the `WithLp 2` product space
used by cone separation. -/
noncomputable def symmPsdScalarProperConeL2 (n : ℕ) :
    ProperCone ℝ (WithLp 2 (SymmMat n × ℝ)) :=
  { toSubmodule :=
      { carrier := {p | p.fst.1.PosSemidef ∧ 0 ≤ p.snd}
        zero_mem' := by
          constructor
          · simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
          · simp
        add_mem' := by
          intro x y hx hy
          constructor
          · exact hx.1.add hy.1
          · simpa using add_nonneg hx.2 hy.2
        smul_mem' := by
          intro a x hx
          constructor
          · exact hx.1.smul a.2
          · simpa [smul_eq_mul] using mul_nonneg a.2 hx.2 }
    isClosed' := by
      have hMatrix : IsClosed {X : SymmMat n | X.1.PosSemidef} := by
        -- The symmetric PSD cone is already closed; this line only rewrites its carrier set.
        have hEq : ({X : SymmMat n | X.1.PosSemidef} : Set (SymmMat n)) = symmPsdProperCone n := by
          ext X
          exact (mem_symmPsdProperCone_iff X).symm
        rw [hEq]
        exact (symmPsdProperCone n).isClosed
      have hScalar : IsClosed {τ : ℝ | 0 ≤ τ} := isClosed_Ici
      simpa [Set.preimage, Set.setOf_and]
        using (hMatrix.preimage (WithLp.fstL 2 ℝ (SymmMat n) ℝ).continuous).inter
          (hScalar.preimage (WithLp.sndL 2 ℝ (SymmMat n) ℝ).continuous) }

/-- Helper for Theorem 10.1: `WithLp 2` cone membership is exactly PSD in the matrix coordinate
together with a nonnegative scale. -/
lemma mem_symmPsdScalarProperConeL2_iff
    (X : SymmMat n) (τ : ℝ) :
    WithLp.toLp 2 (X, τ) ∈ symmPsdScalarProperConeL2 n ↔ X.1.PosSemidef ∧ 0 ≤ τ := by
  -- The `WithLp 2` wrapper keeps the same coordinate-level cone condition.
  rfl

/-- Helper for Theorem 10.1: the `WithLp 2` homogenized cone is self-dual in the coordinates
needed by the separator normalization step. -/
lemma mem_innerDual_symmPsdScalarProperConeL2_iff
    (p : WithLp 2 (SymmMat n × ℝ)) :
    p ∈ ProperCone.innerDual (symmPsdScalarProperConeL2 n : Set (WithLp 2 (SymmMat n × ℝ))) ↔
      p.fst.1.PosSemidef ∧ 0 ≤ p.snd := by
  constructor
  · intro hp
    have hMatrix : p.fst ∈ symmPsdProperCone n := by
      -- Test the separator against the rank-one generators in the matrix coordinate.
      rw [symmPsdProperCone, ProperCone.mem_innerDual]
      intro X hX
      rcases hX with ⟨u, rfl⟩
      have hmem :
          WithLp.toLp 2 (rankOneSymmGenerator u, (0 : ℝ)) ∈ symmPsdScalarProperConeL2 n := by
        have hpsd : (rankOneSymmGenerator u).1.PosSemidef := by
          simpa using Matrix.posSemidef_vecMulVec_self_star u
        exact ((mem_symmPsdScalarProperConeL2_iff (n := n) (rankOneSymmGenerator u) 0).2
          ⟨hpsd, le_rfl⟩)
      have hinner : 0 ≤ inner ℝ (WithLp.toLp 2 (rankOneSymmGenerator u, (0 : ℝ))) p :=
        (ProperCone.mem_innerDual.mp hp) hmem
      simpa [WithLp.prod_inner_apply] using hinner
    have hScalar : 0 ≤ p.snd := by
      -- Testing against the pure-scale direction isolates the scalar coordinate.
      have hmem :
          WithLp.toLp 2 ((0 : SymmMat n), (1 : ℝ)) ∈ symmPsdScalarProperConeL2 n := by
        have hpsd : (0 : SymmMat n).1.PosSemidef := by
          simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
        exact ((mem_symmPsdScalarProperConeL2_iff (n := n) 0 1).2
          ⟨hpsd, zero_le_one⟩)
      have hinner : 0 ≤ inner ℝ (WithLp.toLp 2 ((0 : SymmMat n), (1 : ℝ))) p :=
        (ProperCone.mem_innerDual.mp hp) hmem
      simpa [WithLp.prod_inner_apply] using hinner
    exact ⟨(mem_symmPsdProperCone_iff p.fst).1 hMatrix, hScalar⟩
  · rintro ⟨hpMatrix, hpScalar⟩
    -- Split the `WithLp 2` inner product into its matrix and scalar contributions.
    rw [ProperCone.mem_innerDual]
    intro z hz
    have hz' : z.fst.1.PosSemidef ∧ 0 ≤ z.snd := by
      simpa [WithLp.toLp_ofLp] using
        (mem_symmPsdScalarProperConeL2_iff (n := n) z.fst z.snd).1 hz
    have hMatrix : 0 ≤ inner ℝ z.fst p.fst :=
      inner_symmMat_nonneg_of_posSemidef hz'.1 hpMatrix
    have hScalar : 0 ≤ p.snd * z.snd := by
      simpa [mul_comm] using mul_nonneg hz'.2 hpScalar
    simpa [WithLp.prod_inner_apply] using add_nonneg hMatrix hScalar

/-- Helper for Theorem 10.1: a linear combination of symmetric SDP data is still symmetric. -/
lemma linearCombination_isSymm
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) (y : Fin m → ℝ) (μ : ℝ) :
    ((∑ i, y i • A i) + μ • C).IsSymm := by
  -- Symmetry is preserved by the finite linear combination and the final scalar multiple of `C`.
  have hsum : (∑ i, y i • A i).IsSymm := by
    refine Matrix.IsSymm.ext fun i j ↦ ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [(hA k).apply i j]
  exact hsum.add (hC.smul μ)

/-- Helper for Theorem 10.1: the separator slack matrix is a positive scalar multiple of the dual
slack at the normalized witness `(-μ)⁻¹ • y`. -/
lemma linearCombination_eq_negScale_dualSlack
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin m → ℝ) (μ : ℝ) (hμ : μ ≠ 0) :
    (∑ i, y i • A i) + μ • C =
      (-μ) • sdp_dual_slack A C (((-μ)⁻¹) • y) := by
  -- Expand the normalized slack once so later proofs can divide by `-μ` without redoing algebra.
  calc
    (∑ i, y i • A i) + μ • C
        = (∑ i, (μ * (μ⁻¹ * y i)) • A i) + μ • C := by
            refine congrArg (fun M => M + μ • C) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hcoeff : μ * (μ⁻¹ * y i) = y i := by
              calc
                μ * (μ⁻¹ * y i) = (μ * μ⁻¹) * y i := by ring
                _ = y i := by rw [mul_inv_cancel₀ hμ, one_mul]
            simp [hcoeff]
    _ = (-μ) • (∑ i, (((-μ)⁻¹) • y) i • A i) - (-μ) • C := by
          rw [Finset.smul_sum]
          simp [sub_eq_add_neg, smul_smul, add_comm]
    _ = (-μ) • sdp_dual_slack A C (((-μ)⁻¹) • y) := by
          simp [sdp_dual_slack, smul_sub]

/-- Helper for Theorem 10.1: normalizing a separator rescales the dual objective by the same
factor. -/
lemma sdpDualObjective_smul
    (b : Fin m → ℝ) (a : ℝ) (y : Fin m → ℝ) :
    sdp_dual_objective b (a • y) = a * sdp_dual_objective b y := by
  -- The dual objective is linear in the vector variable.
  calc
    sdp_dual_objective b (a • y) = ∑ i, (a * y i) * b i := by
      simp [sdp_dual_objective]
    _ = ∑ i, a * (y i * b i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = a * ∑ i, y i * b i := by
          rw [Finset.mul_sum]
    _ = a * sdp_dual_objective b y := by
          rfl

/-- Helper for Theorem 10.1: the symmetric trace-constraint map landing in the right-hand side
space `Fin m → ℝ`. -/
noncomputable def sdpConstraintMap
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : SymmMat n →L[ℝ] (Fin m → ℝ) :=
  let L : SymmMat n →ₗ[ℝ] Fin m → ℝ :=
    { toFun := fun X i => Matrix.trace (A i * X.1)
      map_add' := by
        intro X Y
        ext i
        -- Each coordinate is linear because trace respects addition in the matrix argument.
        simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro r X
        ext i
        -- Pull the scalar through the matrix product and the trace.
        simp [Matrix.trace_smul] }
  ⟨L, L.continuous_of_finiteDimensional⟩

/-- Helper for Theorem 10.1: evaluating the symmetric trace-constraint map just replays the trace
constraints on the underlying matrix. -/
lemma sdpConstraintMap_apply
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (X : SymmMat n) (i : Fin m) :
    sdpConstraintMap A X i = Matrix.trace (A i * X.1) := rfl

/-- Helper for Theorem 10.1: the objective trace map on the symmetric ambient space. -/
noncomputable def sdpObjectiveMap
    (C : Matrix (Fin n) (Fin n) ℝ) : SymmMat n →L[ℝ] ℝ :=
  let L : SymmMat n →ₗ[ℝ] ℝ :=
    { toFun := fun X => Matrix.trace (C * X.1)
      map_add' := by
        intro X Y
        -- The objective is linear in the matrix variable.
        simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro r X
        -- Again the scalar moves through matrix multiplication and trace.
        simp [Matrix.trace_smul] }
  ⟨L, L.continuous_of_finiteDimensional⟩

/-- Helper for Theorem 10.1: evaluating the symmetric objective map is the textbook trace
objective on the underlying matrix. -/
lemma sdpObjectiveMap_apply
    (C : Matrix (Fin n) (Fin n) ℝ) (X : SymmMat n) :
    sdpObjectiveMap C X = Matrix.trace (C * X.1) := rfl

/-- Helper for Theorem 10.1: a strict primal witness can be packaged directly in the symmetric
ambient space used by the separator argument. -/
lemma exists_strictSymmPrimalWitness
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (hstrict : sdp_primal_strictly_feasible A b) :
    ∃ X₀ : SymmMat n, X₀.1.PosDef ∧ ∀ i, Matrix.trace (A i * X₀.1) = b i := by
  rcases hstrict with ⟨X₀, hX₀, hAX₀⟩
  -- Repackage the positive-definite witness as an element of the symmetric subspace once.
  exact ⟨⟨X₀, by simpa using hX₀.isHermitian⟩, hX₀, hAX₀⟩

/-- Helper for Theorem 10.1: the symmetric constraint map onto its actual range admits a
continuous right inverse in finite dimension. -/
noncomputable def constraintRangeRightInversePackage
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    { g : (sdpConstraintMap A).range →L[ℝ] SymmMat n //
      Function.RightInverse g ((sdpConstraintMap A).rangeRestrict) } := by
  let hsurj : Function.Surjective (((sdpConstraintMap A).rangeRestrict).toLinearMap) := by
    intro u
    rcases u with ⟨u, hu⟩
    rcases hu with ⟨X, rfl⟩
    exact ⟨X, rfl⟩
  let hsplit :
      ∃ g : (sdpConstraintMap A).range →ₗ[ℝ] SymmMat n,
        ((sdpConstraintMap A).rangeRestrict.toLinearMap).comp g = LinearMap.id := by
    exact ((sdpConstraintMap A).rangeRestrict.toLinearMap).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 hsurj)
  refine ⟨⟨Classical.choose hsplit, (Classical.choose hsplit).continuous_of_finiteDimensional⟩, ?_⟩
  -- Convert the chosen linear splitting into the pointwise right-inverse identity we use later.
  exact LinearMap.ext_iff.1 (Classical.choose_spec hsplit)

/-- Helper for Theorem 10.1: choose a continuous right inverse on the range of the symmetric
constraint map. -/
noncomputable def constraintRangeRightInverse
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    (sdpConstraintMap A).range →L[ℝ] SymmMat n :=
  (constraintRangeRightInversePackage A).1

/-- Helper for Theorem 10.1: the chosen right inverse really splits the range-restricted
constraint map. -/
lemma sdpConstraintMap_rangeRightInverse_apply
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (u : (sdpConstraintMap A).range) :
    (sdpConstraintMap A).rangeRestrict (constraintRangeRightInverse A u) = u :=
  (constraintRangeRightInversePackage A).2 u

/-- Helper for Theorem 10.1: after forgetting the subtype wrapper, the chosen right inverse sends
each residual in the range back to a symmetric matrix with that residual. -/
lemma sdpConstraintMap_constraintRangeRightInverse
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (u : (sdpConstraintMap A).range) :
    sdpConstraintMap A (constraintRangeRightInverse A u) = u := by
  -- Compare in the subtype-valued range first, then strip the coercion.
  exact congrArg Subtype.val (sdpConstraintMap_rangeRightInverse_apply A u)

/-- Helper for Theorem 10.1: once one feasible symmetric witness is fixed, every primal residual
vector belongs to the actual range of the symmetric constraint map. -/
lemma primalResidual_mem_constraintRange
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    {X₀ : SymmMat n} (hX₀ : ∀ i, Matrix.trace (A i * X₀.1) = b i)
    (X : SymmMat n) (τ : ℝ) :
    (fun i => Matrix.trace (A i * X.1) - τ * b i) ∈ Set.range (sdpConstraintMap A) := by
  refine ⟨X - τ • X₀, ?_⟩
  ext i
  -- Subtract the fixed feasible witness to rewrite the residual as an actual constraint value.
  calc
    sdpConstraintMap A (X - τ • X₀) i
        = Matrix.trace (A i * ((X - τ • X₀ : SymmMat n).1)) := by
            rfl
    _ = Matrix.trace (A i * X.1) - Matrix.trace (A i * (τ • X₀.1)) := by
          rw [show ((X - τ • X₀ : SymmMat n).1) = X.1 - τ • X₀.1 by rfl]
          rw [Matrix.mul_sub, Matrix.trace_sub]
    _ = Matrix.trace (A i * X.1) - τ * Matrix.trace (A i * X₀.1) := by
          rw [Matrix.mul_smul, Matrix.trace_smul]
          simp [smul_eq_mul]
    _ = Matrix.trace (A i * X.1) - τ * b i := by rw [hX₀ i]

/-- Helper for Theorem 10.1: the homogenization scale map `τ ↦ τ b`. -/
noncomputable def rhsScaleMap
    (b : Fin m → ℝ) : ℝ →L[ℝ] (Fin m → ℝ) :=
  let L : ℝ →ₗ[ℝ] Fin m → ℝ :=
    { toFun := fun τ i => τ * b i
      map_add' := by
        intro τ σ
        ext i
        -- The right-hand side scales coordinatewise.
        simp [add_mul]
      map_smul' := by
        intro r τ
        ext i
        -- Scalar multiplication on the scale coordinate is ordinary multiplication.
        simp [smul_eq_mul, mul_assoc] }
  ⟨L, L.continuous_of_finiteDimensional⟩

/-- Helper for Theorem 10.1: evaluating the right-hand-side scale map produces the coordinatewise
product `τ b`. -/
lemma rhsScaleMap_apply
    (b : Fin m → ℝ) (τ : ℝ) (i : Fin m) :
    rhsScaleMap b τ i = τ * b i := rfl

/-- Helper for Theorem 10.1: the projected homogenized primal map used for cone separation. -/
noncomputable def primalHomogenizedSdpMap
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    (SymmMat n × ℝ) →L[ℝ] (Fin m → ℝ) × ℝ :=
  (((sdpConstraintMap A).comp (ContinuousLinearMap.fst ℝ (SymmMat n) ℝ)) -
      ((rhsScaleMap b).comp (ContinuousLinearMap.snd ℝ (SymmMat n) ℝ))).prod
    (((sdpObjectiveMap C).comp (ContinuousLinearMap.fst ℝ (SymmMat n) ℝ)) -
      α • (ContinuousLinearMap.snd ℝ (SymmMat n) ℝ))

/-- Helper for Theorem 10.1: the projected homogenized map records the primal constraint residual
and the objective gap against `α`. -/
lemma primalHomogenizedSdpMap_apply
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (X : SymmMat n) (τ : ℝ) :
    primalHomogenizedSdpMap A b C α (X, τ) =
      (fun i => Matrix.trace (A i * X.1) - τ * b i, Matrix.trace (C * X.1) - α * τ) := by
  -- Unfold the product map once so later separation lemmas can rewrite by a single formula.
  ext i <;> simp [primalHomogenizedSdpMap, sdpConstraintMap, rhsScaleMap, sdpObjectiveMap]

/-- Helper for Theorem 10.1: the canonical finite-dimensional inclusion of a constraint vector
into its Euclidean `L²` realization. -/
noncomputable def constraintVectorToEuclidean (m : ℕ) :
    (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap

/-- Helper for Theorem 10.1: the corrected `WithLp 2` version of the homogenized primal map used
by the cone-separation theorem. -/
noncomputable def primalHomogenizedSdpMapL2
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    WithLp 2 (SymmMat n × ℝ) →L[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin m) × ℝ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin m)) ℝ).symm :
      (EuclideanSpace ℝ (Fin m) × ℝ) →L[ℝ]
        WithLp 2 (EuclideanSpace ℝ (Fin m) × ℝ)) ∘L
    (((constraintVectorToEuclidean m).comp
        (ContinuousLinearMap.fst ℝ (Fin m → ℝ) ℝ)).prod
      (ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ)) ∘L
    primalHomogenizedSdpMap A b C α ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℝ (SymmMat n) ℝ :
        WithLp 2 (SymmMat n × ℝ) →L[ℝ] SymmMat n × ℝ)

/-- Helper for Theorem 10.1: evaluating the `WithLp 2` homogenized map recovers the same
constraint residual and objective gap as the plain-product version. -/
lemma primalHomogenizedSdpMapL2_apply
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (z : WithLp 2 (SymmMat n × ℝ)) :
    primalHomogenizedSdpMapL2 A b C α z =
      WithLp.toLp 2
        (WithLp.toLp 2 (fun i => Matrix.trace (A i * z.fst.1) - z.snd * b i),
          Matrix.trace (C * z.fst.1) - α * z.snd) := by
  -- Transport the plain-product coordinate formula through the canonical `WithLp 2` equivalences.
  rw [primalHomogenizedSdpMapL2]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [primalHomogenizedSdpMap_apply]
  rfl

/-- Helper for Theorem 10.1: the graph homogenized map appends the explicit scale coordinate to the
projected separation map. -/
noncomputable def primalHomogenizedGraphMap
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    (SymmMat n × ℝ) →L[ℝ] ((Fin m → ℝ) × ℝ) × ℝ :=
  (primalHomogenizedSdpMap A b C α).prod (ContinuousLinearMap.snd ℝ (SymmMat n) ℝ)

/-- Helper for Theorem 10.1: the graph map keeps the projected residuals and remembers the scale
coordinate explicitly. -/
lemma primalHomogenizedGraphMap_apply
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (X : SymmMat n) (τ : ℝ) :
    primalHomogenizedGraphMap A b C α (X, τ) =
      ((fun i => Matrix.trace (A i * X.1) - τ * b i, Matrix.trace (C * X.1) - α * τ), τ) := by
  -- The graph map is just the projected map together with the remembered homogenization scale.
  simp [primalHomogenizedGraphMap, primalHomogenizedSdpMap_apply]

/-- Helper for Theorem 10.1: every dual-feasible objective value bounds the primal supremum from
above once the primal problem is strictly feasible. -/
lemma csSup_primalValues_le_dualObjective_of_dualFeasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hstrict : sdp_primal_strictly_feasible A b) {y : Fin m → ℝ}
    (hy : y ∈ sdp_dual_feasible_region A C) :
    sSup (sdp_primal_objective_values A b C) ≤ sdp_dual_objective b y := by
  rcases
      sdp_primal_strictly_feasible.exists_mem_primal_feasible_region A b hstrict with
    ⟨X₀, hX₀, _⟩
  have hnonempty : (sdp_primal_objective_values A b C).Nonempty := by
    exact ⟨sdp_primal_objective C X₀, ⟨X₀, hX₀, rfl⟩⟩
  -- Weak duality bounds every attainable primal value by the chosen dual-feasible objective.
  refine csSup_le hnonempty ?_
  intro z hz
  rcases (mem_sdp_primal_objective_values_iff A b C z).1 hz with ⟨X, hX, rfl⟩
  exact sdpWeakDualityFeasiblePair A b C hX hy

/-- Helper for Theorem 10.1: every primal-feasible objective value lies below the dual infimum
once the dual problem is strictly feasible. -/
lemma primalObjective_le_csInf_dualValues_of_primalFeasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hstrict : sdp_dual_strictly_feasible A C) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ sdp_primal_feasible_region A b) :
    sdp_primal_objective C X ≤ sInf (sdp_dual_objective_values A b C) := by
  rcases sdp_dual_strictly_feasible.exists_mem_dual_feasible_region A C hstrict with
    ⟨y₀, hy₀, _⟩
  have hnonempty : (sdp_dual_objective_values A b C).Nonempty := by
    exact ⟨sdp_dual_objective b y₀, ⟨y₀, hy₀, rfl⟩⟩
  -- Weak duality supplies the lower bound against every dual-feasible value.
  refine le_csInf hnonempty ?_
  intro z hz
  rcases (mem_sdp_dual_objective_values_iff A b C z).1 hz with ⟨y, hy, rfl⟩
  exact sdpWeakDualityFeasiblePair A b C hX hy

/-- Helper for Theorem 10.1: an exact primal homogenized point with zero constraint residual
cannot have positive objective gap above the supremum. -/
lemma primalGap_nonpos_of_exactResidual
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hstrict : sdp_primal_strictly_feasible A b)
    (hbounded : BddAbove (sdp_primal_objective_values A b C))
    {X : SymmMat n} {τ : ℝ}
    (hX : X.1.PosSemidef) (hτ : 0 ≤ τ)
    (hres : ∀ i, Matrix.trace (A i * X.1) = τ * b i) :
    Matrix.trace (C * X.1) - sSup (sdp_primal_objective_values A b C) * τ ≤ 0 := by
  let α := sSup (sdp_primal_objective_values A b C)
  by_cases hτzero : τ = 0
  · have hobj_nonpos : Matrix.trace (C * X.1) ≤ 0 := by
      by_contra hobj_pos
      rcases
          sdp_primal_strictly_feasible.exists_mem_primal_feasible_region A b hstrict with
        ⟨X₀, hX₀, _⟩
      rcases hbounded with ⟨M, hM⟩
      obtain ⟨k, hk⟩ :=
        exists_nat_gt ((M - sdp_primal_objective C X₀) / Matrix.trace (C * X.1))
      have hkReal :
          (M - sdp_primal_objective C X₀) / Matrix.trace (C * X.1) < (k : ℝ) := by
        exact_mod_cast hk
      have hgap :
          M - sdp_primal_objective C X₀ < (k : ℝ) * Matrix.trace (C * X.1) := by
        exact (div_lt_iff₀ (show 0 < Matrix.trace (C * X.1) from lt_of_not_ge hobj_pos)).mp hkReal
      have hkAbove :
          M < sdp_primal_objective C X₀ + (k : ℝ) * Matrix.trace (C * X.1) := by
        have := add_lt_add_right hgap (sdp_primal_objective C X₀)
        simpa [sdp_primal_objective, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have hfeasible :
          X₀ + (k : ℝ) • X.1 ∈ sdp_primal_feasible_region A b := by
        constructor
        · exact hX₀.1.add (hX.smul (show 0 ≤ (k : ℝ) by positivity))
        · intro i
          calc
            Matrix.trace (A i * (X₀ + (k : ℝ) • X.1))
                = Matrix.trace (A i * X₀) + Matrix.trace (A i * ((k : ℝ) • X.1)) := by
                    rw [Matrix.mul_add, Matrix.trace_add]
            _ = b i + (k : ℝ) * Matrix.trace (A i * X.1) := by
                  rw [hX₀.2 i, Matrix.mul_smul, Matrix.trace_smul]
                  simp [smul_eq_mul]
            _ = b i := by
                  rw [hres i, hτzero]
                  ring
      have hvalueMem :
          sdp_primal_objective C (X₀ + (k : ℝ) • X.1) ∈ sdp_primal_objective_values A b C := by
        exact ⟨X₀ + (k : ℝ) • X.1, hfeasible, rfl⟩
      have hvalueEq :
          sdp_primal_objective C (X₀ + (k : ℝ) • X.1) =
            sdp_primal_objective C X₀ + (k : ℝ) * Matrix.trace (C * X.1) := by
        calc
          sdp_primal_objective C (X₀ + (k : ℝ) • X.1)
              = Matrix.trace (C * X₀) + Matrix.trace (C * ((k : ℝ) • X.1)) := by
                  simp [sdp_primal_objective, Matrix.mul_add, Matrix.trace_add]
          _ = sdp_primal_objective C X₀ + (k : ℝ) * Matrix.trace (C * X.1) := by
                rw [sdp_primal_objective, Matrix.mul_smul, Matrix.trace_smul]
                simp [smul_eq_mul]
      have hcontr : sdp_primal_objective C (X₀ + (k : ℝ) • X.1) ≤ M := hM hvalueMem
      rw [hvalueEq] at hcontr
      exact (not_lt_of_ge hcontr) hkAbove
    simpa [α, hτzero] using hobj_nonpos
  · have hτpos : 0 < τ := lt_of_le_of_ne hτ (by simpa [eq_comm] using hτzero)
    have hfeasible : τ⁻¹ • X.1 ∈ sdp_primal_feasible_region A b := by
      constructor
      · exact hX.smul (inv_nonneg.mpr hτ)
      · intro i
        calc
          Matrix.trace (A i * (τ⁻¹ • X.1))
              = τ⁻¹ * Matrix.trace (A i * X.1) := by
                  rw [Matrix.mul_smul, Matrix.trace_smul]
                  simp [smul_eq_mul]
          _ = τ⁻¹ * (τ * b i) := by rw [hres i]
          _ = b i := by field_simp [hτzero]
    have hmem :
        sdp_primal_objective C (τ⁻¹ • X.1) ∈ sdp_primal_objective_values A b C := by
      exact ⟨τ⁻¹ • X.1, hfeasible, rfl⟩
    have hle : sdp_primal_objective C (τ⁻¹ • X.1) ≤ α := le_csSup hbounded hmem
    have hscaled :
        τ⁻¹ * Matrix.trace (C * X.1) ≤ α := by
      simpa [sdp_primal_objective, Matrix.mul_smul, Matrix.trace_smul] using hle
    have hscaled' : Matrix.trace (C * X.1) / τ ≤ α := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
    have hfinal : Matrix.trace (C * X.1) ≤ α * τ := by
      exact (div_le_iff₀ hτpos).mp hscaled'
    simpa [α, sub_le_iff_le_add'] using hfinal

/-- Helper for Theorem 10.1: the exact image of the primal homogenized map already avoids the gap
point `(0,1)`; the remaining certificate blocker is only closure under `ProperCone.map`. -/
lemma gapPoint_notIn_primalHomogenizedExactImageL2
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hstrict : sdp_primal_strictly_feasible A b)
    (hbounded : BddAbove (sdp_primal_objective_values A b C)) :
    ¬ ∃ z : WithLp 2 (SymmMat n × ℝ),
      z ∈ symmPsdScalarProperConeL2 n ∧
        primalHomogenizedSdpMapL2 A b C (sSup (sdp_primal_objective_values A b C)) z =
          WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin m)), (1 : ℝ)) := by
  intro hgap
  rcases hgap with ⟨z, hzCone, hzEq⟩
  have hzMem : z.fst.1.PosSemidef ∧ 0 ≤ z.snd := by
    simpa [WithLp.toLp_ofLp] using
      (mem_symmPsdScalarProperConeL2_iff (n := n) z.fst z.snd).1 hzCone
  have hzCoords :
      (WithLp.toLp 2 (fun i => Matrix.trace (A i * z.fst.1) - z.snd * b i),
        Matrix.trace (C * z.fst.1) -
          sSup (sdp_primal_objective_values A b C) * z.snd) =
        ((0 : EuclideanSpace ℝ (Fin m)), (1 : ℝ)) := by
    exact WithLp.toLp_injective (2 : ENNReal) <|
      by simpa [primalHomogenizedSdpMapL2_apply] using hzEq
  have hzResidual :
      (fun i => Matrix.trace (A i * z.fst.1) - z.snd * b i) = (0 : Fin m → ℝ) :=
    congrArg WithLp.ofLp (congrArg Prod.fst hzCoords)
  have hzGap :
      Matrix.trace (C * z.fst.1) -
          sSup (sdp_primal_objective_values A b C) * z.snd = (1 : ℝ) :=
    congrArg Prod.snd hzCoords
  have hres : ∀ i, Matrix.trace (A i * z.fst.1) = z.snd * b i := by
    intro i
    have hi := congrFun hzResidual i
    simpa using sub_eq_zero.mp hi
  have hgapNonpos :
      Matrix.trace (C * z.fst.1) -
          sSup (sdp_primal_objective_values A b C) * z.snd ≤ 0 :=
    primalGap_nonpos_of_exactResidual A b C hstrict hbounded hzMem.1 hzMem.2 hres
  have hscalar : Matrix.trace (C * z.fst.1) -
      sSup (sdp_primal_objective_values A b C) * z.snd = 1 := by
    simpa using hzGap
  exact (not_le_of_gt zero_lt_one) (by simpa [hscalar] using hgapNonpos)

/-- Helper for Theorem 10.1: the symmetrized outer product as a raw matrix-valued bilinear map. -/
def symmetrizedVecMulVecRawBilin (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  vecMulVecBilin ℝ ℝ + LinearMap.flip (vecMulVecBilin ℝ ℝ)

/-- Helper for Theorem 10.1: every value of the symmetrized outer-product bilinear map is
symmetric. -/
lemma symmetrizedVecMulVecRawBilin_isSymm
    (u v : Fin n → ℝ) :
    (symmetrizedVecMulVecRawBilin n u v).IsSymm := by
  -- Swapping the matrix indices exchanges the two summands.
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  simp [symmetrizedVecMulVecRawBilin, Matrix.vecMulVec_apply, add_comm, mul_comm]

/-- Helper for Theorem 10.1: fixing the first vector in the symmetrized outer product gives a
linear map into symmetric matrices. -/
def symmetrizedVecMulVecRight (u : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] SymmMat n :=
  (symmetrizedVecMulVecRawBilin n u).codRestrict
    (symmSubmodule n) (symmetrizedVecMulVecRawBilin_isSymm u)

/-- Helper for Theorem 10.1: the symmetric outer-product linear maps add in their first
argument. -/
lemma symmetrizedVecMulVecRight_add
    (u v : Fin n → ℝ) :
    symmetrizedVecMulVecRight (u + v) =
      symmetrizedVecMulVecRight u + symmetrizedVecMulVecRight v := by
  -- Equality follows after forgetting the symmetric-subtype wrapper.
  ext w i j
  simp [symmetrizedVecMulVecRight, symmetrizedVecMulVecRawBilin]
  ring

/-- Helper for Theorem 10.1: the symmetric outer-product linear maps scale in their first
argument. -/
lemma symmetrizedVecMulVecRight_smul
    (a : ℝ) (u : Fin n → ℝ) :
    symmetrizedVecMulVecRight (a • u) = a • symmetrizedVecMulVecRight u := by
  -- Equality follows after forgetting the symmetric-subtype wrapper.
  ext v i j
  simp [symmetrizedVecMulVecRight, symmetrizedVecMulVecRawBilin]
  ring

/-- Helper for Theorem 10.1: the symmetrized outer product as a bilinear map valued in
`SymmMat n`. -/
def symmetrizedVecMulVecBilin (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] SymmMat n where
  toFun := symmetrizedVecMulVecRight
  map_add' := symmetrizedVecMulVecRight_add
  map_smul' := symmetrizedVecMulVecRight_smul

/-- Helper for Theorem 10.1: on the diagonal, half the symmetrized outer product is the canonical
rank-one symmetric generator. -/
lemma half_symmetrizedVecMulVecBilin_self
    (u : Fin n → ℝ) :
    (2 : ℝ)⁻¹ • symmetrizedVecMulVecBilin n u u = rankOneSymmGenerator u := by
  -- Both summands coincide on the diagonal, so the factor `2⁻¹` cancels their sum.
  ext i j
  simp [symmetrizedVecMulVecBilin, symmetrizedVecMulVecRight,
    symmetrizedVecMulVecRawBilin, rankOneSymmGenerator, Matrix.vecMulVec_apply]
  ring

/-- Helper for Theorem 10.1: a positive-definite symmetric matrix has a norm neighborhood
contained in the positive-semidefinite cone. -/
lemma strictWitnessRadius
    (X₀ : SymmMat n) (hX₀ : X₀.1.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ Δ : SymmMat n, ‖Δ‖ ≤ ε → (X₀ + Δ).1.PosSemidef := by
  classical
  let q : (Fin n → ℝ) → ℝ := fun u ↦ u ⬝ᵥ (X₀.1 *ᵥ u)
  have hqContinuous : Continuous q := by
    -- The quadratic form is a finite sum of products of coordinate maps.
    fun_prop
  have hqPositive :
      ∀ u ∈ Metric.sphere (0 : Fin n → ℝ) 1, 0 < q u := by
    intro u hu
    have huNorm : ‖u‖ = 1 := by simpa [Metric.mem_sphere] using hu
    have huNe : u ≠ 0 := by
      intro huZero
      simp [huZero] at huNorm
    simpa [q] using hX₀.dotProduct_mulVec_pos huNe
  obtain ⟨δ, hδ, hδLower⟩ :=
    (isCompact_sphere (0 : Fin n → ℝ) 1).exists_forall_le'
      hqContinuous.continuousOn hqPositive
  let g : (Fin n → ℝ) → ℝ := fun u ↦ ‖rankOneSymmGenerator u‖
  have hgContinuous : Continuous g := by
    -- The rank-one generator and its norm vary continuously with the vector.
    let B₀ : (Fin n → ℝ) →ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] SymmMat n) :=
      (LinearMap.toContinuousLinearMap :
          ((Fin n → ℝ) →ₗ[ℝ] SymmMat n) ≃ₗ[ℝ]
            ((Fin n → ℝ) →L[ℝ] SymmMat n)).toLinearMap.comp
        (symmetrizedVecMulVecBilin n)
    let B : (Fin n → ℝ) →L[ℝ]
        ((Fin n → ℝ) →L[ℝ] SymmMat n) :=
      LinearMap.toContinuousLinearMap B₀
    have hdiag : Continuous (fun u : Fin n → ℝ ↦ B u u) := by
      exact isBoundedBilinearMap_apply.continuous.comp
        (B.continuous.prodMk continuous_id)
    have hscaled : Continuous (fun u : Fin n → ℝ ↦ (2 : ℝ)⁻¹ • B u u) :=
      (continuous_const_smul _).comp hdiag
    have hgenerator : (fun u : Fin n → ℝ ↦ (2 : ℝ)⁻¹ • B u u) =
        rankOneSymmGenerator := by
      funext u
      exact half_symmetrizedVecMulVecBilin_self u
    rw [hgenerator] at hscaled
    exact hscaled.norm
  obtain ⟨B₀, hB₀⟩ :=
    (isCompact_sphere (0 : Fin n → ℝ) 1).bddAbove_image hgContinuous.continuousOn
  let B : ℝ := |B₀| + 1
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨δ / B, div_pos hδ hB, ?_⟩
  intro Δ hΔ
  have hunitNonneg :
      ∀ u ∈ Metric.sphere (0 : Fin n → ℝ) 1,
        0 ≤ u ⬝ᵥ ((X₀ + Δ).1 *ᵥ u) := by
    intro u hu
    have huRank : ‖rankOneSymmGenerator u‖ ≤ B := by
      have hle : g u ≤ B₀ := hB₀ (Set.mem_image_of_mem g hu)
      have hB₀abs : B₀ ≤ |B₀| := le_abs_self B₀
      dsimp [B, g] at hle ⊢
      linarith
    have hinnerAbs :
        |inner ℝ (rankOneSymmGenerator u) Δ| ≤ B * ‖Δ‖ := by
      calc
        |inner ℝ (rankOneSymmGenerator u) Δ|
            ≤ ‖rankOneSymmGenerator u‖ * ‖Δ‖ := abs_real_inner_le_norm _ _
        _ ≤ B * ‖Δ‖ := by
              exact mul_le_mul_of_nonneg_right huRank (norm_nonneg Δ)
    have hinnerLower : -δ ≤ inner ℝ (rankOneSymmGenerator u) Δ := by
      have hBΔ : B * ‖Δ‖ ≤ δ := by
        calc
          B * ‖Δ‖ ≤ B * (δ / B) :=
            mul_le_mul_of_nonneg_left hΔ hB.le
          _ = δ := by field_simp
      exact le_trans (neg_le_neg hBΔ) (neg_le_of_abs_le hinnerAbs)
    have hqLower : δ ≤ q u := hδLower u hu
    have hsum :
        0 ≤ q u + inner ℝ (rankOneSymmGenerator u) Δ := by
      linarith
    rw [rankOneSymmGenerator_inner_eq_dotProduct_mulVec] at hsum
    calc
      0 ≤ q u + u ⬝ᵥ (Δ.1 *ᵥ u) := hsum
      _ = u ⬝ᵥ ((X₀ + Δ).1 *ᵥ u) := by
        simp [q, Matrix.add_mulVec, dotProduct_add]
  -- Normalize an arbitrary nonzero vector to the unit sphere and rescale its quadratic form.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.ext fun i j ↦ by
      simpa using ((X₀ + Δ).2.apply i j)
  · intro u
    suffices 0 ≤ u ⬝ᵥ ((X₀ + Δ).1 *ᵥ u) by simpa using this
    by_cases hu : u = 0
    · simp [hu]
    · let w : Fin n → ℝ := ‖u‖⁻¹ • u
      have huNormPos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hwNorm : ‖w‖ = 1 := by
        simp [w, norm_smul, huNormPos.ne']
      have hwSphere : w ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
        simpa [Metric.mem_sphere] using hwNorm
      have hwNonneg := hunitNonneg w hwSphere
      have huEq : u = ‖u‖ • w := by
        ext i
        simp [w, huNormPos.ne']
      rw [huEq]
      simpa [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        pow_two, mul_assoc] using mul_nonneg (sq_nonneg ‖u‖) hwNonneg

/-- Helper for Theorem 10.1: a sufficiently large norm-scaled positive-definite witness absorbs
the image of any continuous linear map into symmetric matrices. -/
lemma scaledStrictWitnessCorrectionPosSemidef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E →L[ℝ] SymmMat n) (X₀ : SymmMat n) (hX₀ : X₀.1.PosDef) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ e : E, (((κ * ‖e‖) • X₀) - R e).1.PosSemidef := by
  obtain ⟨ε, hε, hball⟩ := strictWitnessRadius X₀ hX₀
  let κ : ℝ := (‖R‖ + 1) / ε
  have hκ : 0 < κ := by
    exact div_pos (by positivity) hε
  refine ⟨κ, hκ, ?_⟩
  intro e
  by_cases he : e = 0
  · subst he
    simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
  · have heNorm : 0 < ‖e‖ := norm_pos_iff.mpr he
    let a : ℝ := κ * ‖e‖
    have ha : 0 < a := mul_pos hκ heNorm
    let Δ : SymmMat n := -(a⁻¹) • R e
    have hRe : ‖R e‖ ≤ ‖R‖ * ‖e‖ := R.le_opNorm e
    have hΔ : ‖Δ‖ ≤ ε := by
      have hRnonneg : 0 ≤ ‖R‖ := norm_nonneg R
      have hnum : ‖R‖ ≤ ‖R‖ + 1 := by linarith
      have hscale : a = ((‖R‖ + 1) / ε) * ‖e‖ := by rfl
      calc
        ‖Δ‖ = a⁻¹ * ‖R e‖ := by
          simp [Δ, norm_smul, abs_of_pos ha]
        _ ≤ a⁻¹ * (‖R‖ * ‖e‖) :=
          mul_le_mul_of_nonneg_left hRe (inv_nonneg.mpr ha.le)
        _ ≤ a⁻¹ * ((‖R‖ + 1) * ‖e‖) := by
          gcongr
        _ = ε := by
          rw [hscale]
          field_simp
    have hperturbed : (X₀ + Δ).1.PosSemidef := hball Δ hΔ
    have hscaled := hperturbed.smul ha.le
    -- Scaling the normalized perturbation back gives exactly the required correction.
    have hcorrection : a • (X₀ + Δ).1 = (a • X₀ - R e).1 := by
      simp [Δ, smul_add, smul_smul, ha.ne', sub_eq_add_neg]
    rw [hcorrection] at hscaled
    simpa [a] using hscaled

/-- Helper for Theorem 10.1: on the homogenized primal cone, the objective gap is bounded by a
fixed multiple of the constraint-residual norm. -/
lemma primalGap_le_constraintResidualNorm
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hstrict : sdp_primal_strictly_feasible A b)
    (hbounded : BddAbove (sdp_primal_objective_values A b C)) :
    ∃ M : ℝ, 0 < M ∧
      ∀ z : WithLp 2 (SymmMat n × ℝ),
        z ∈ symmPsdScalarProperConeL2 n →
          Matrix.trace (C * z.fst.1) -
              sSup (sdp_primal_objective_values A b C) * z.snd ≤
            M * ‖WithLp.toLp 2
              (fun i ↦ Matrix.trace (A i * z.fst.1) - z.snd * b i)‖ := by
  rcases exists_strictSymmPrimalWitness A b hstrict with ⟨X₀, hX₀pd, hX₀eq⟩
  obtain ⟨κ, hκ, hcorrection⟩ :=
    scaledStrictWitnessCorrectionPosSemidef (constraintRangeRightInverse A) X₀ hX₀pd
  let α := sSup (sdp_primal_objective_values A b C)
  let M : ℝ :=
    ‖sdpObjectiveMap C‖ * ‖constraintRangeRightInverse A‖ +
      κ * |α - sdpObjectiveMap C X₀| + 1
  have hM : 0 < M := by
    have hfirst : 0 ≤ ‖sdpObjectiveMap C‖ * ‖constraintRangeRightInverse A‖ :=
      mul_nonneg (norm_nonneg (sdpObjectiveMap C))
        (norm_nonneg (constraintRangeRightInverse A))
    have hsecond : 0 ≤ κ * |α - sdpObjectiveMap C X₀| :=
      mul_nonneg hκ.le (abs_nonneg _)
    dsimp [M]
    linarith
  refine ⟨M, hM, ?_⟩
  intro z hz
  have hzMem : z.fst.1.PosSemidef ∧ 0 ≤ z.snd := by
    simpa [WithLp.toLp_ofLp] using
      (mem_symmPsdScalarProperConeL2_iff (n := n) z.fst z.snd).1 hz
  let uRaw : Fin m → ℝ :=
    fun i ↦ Matrix.trace (A i * z.fst.1) - z.snd * b i
  have huRange : uRaw ∈ Set.range (sdpConstraintMap A) := by
    exact primalResidual_mem_constraintRange A b hX₀eq z.fst z.snd
  let u : (sdpConstraintMap A).range := ⟨uRaw, huRange⟩
  let Q : SymmMat n := constraintRangeRightInverse A u
  let D : SymmMat n := (κ * ‖u‖) • X₀ - Q
  have hD : D.1.PosSemidef := by
    simpa [D, Q] using hcorrection u
  let X' : SymmMat n := z.fst + D
  let τ' : ℝ := z.snd + κ * ‖u‖
  have hX' : X'.1.PosSemidef := by
    exact hzMem.1.add hD
  have hτ' : 0 ≤ τ' := by
    dsimp [τ']
    exact add_nonneg hzMem.2 (mul_nonneg hκ.le (norm_nonneg u))
  have hQmap : sdpConstraintMap A Q = u := by
    exact sdpConstraintMap_constraintRangeRightInverse A u
  have hres' : ∀ i, Matrix.trace (A i * X'.1) = τ' * b i := by
    intro i
    have hQi := congrFun hQmap i
    calc
      Matrix.trace (A i * X'.1)
          = Matrix.trace (A i * z.fst.1) +
              Matrix.trace (A i * ((κ * ‖u‖) • X₀.1)) -
                Matrix.trace (A i * Q.1) := by
            simp [X', D, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
            ring
      _ = Matrix.trace (A i * z.fst.1) +
              (κ * ‖u‖) * b i - uRaw i := by
            rw [Matrix.mul_smul, Matrix.trace_smul, hX₀eq i]
            simpa [sdpConstraintMap_apply] using hQi
      _ = τ' * b i := by
            simp [uRaw, τ']
            ring
  have hcorrectedGap :
      Matrix.trace (C * X'.1) - α * τ' ≤ 0 := by
    simpa [α] using
      primalGap_nonpos_of_exactResidual A b C hstrict hbounded hX' hτ' hres'
  have hgapIdentity :
      Matrix.trace (C * z.fst.1) - α * z.snd =
        (Matrix.trace (C * X'.1) - α * τ') +
          sdpObjectiveMap C Q + (κ * ‖u‖) * (α - sdpObjectiveMap C X₀) := by
    simp [X', D, τ', sdpObjectiveMap_apply, Matrix.mul_add, Matrix.mul_sub,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul]
    ring
  have hQNorm : ‖Q‖ ≤ ‖constraintRangeRightInverse A‖ * ‖u‖ := by
    exact (constraintRangeRightInverse A).le_opNorm u
  have hObjectiveQ :
      |sdpObjectiveMap C Q| ≤
        ‖sdpObjectiveMap C‖ * ‖constraintRangeRightInverse A‖ * ‖u‖ := by
    calc
      |sdpObjectiveMap C Q| = ‖sdpObjectiveMap C Q‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ‖sdpObjectiveMap C‖ * ‖Q‖ := (sdpObjectiveMap C).le_opNorm Q
      _ ≤ ‖sdpObjectiveMap C‖ *
          (‖constraintRangeRightInverse A‖ * ‖u‖) := by
            exact mul_le_mul_of_nonneg_left hQNorm (norm_nonneg _)
      _ = ‖sdpObjectiveMap C‖ * ‖constraintRangeRightInverse A‖ * ‖u‖ := by
            ring
  have hgapBound :
      Matrix.trace (C * z.fst.1) - α * z.snd ≤
        (‖sdpObjectiveMap C‖ * ‖constraintRangeRightInverse A‖ +
          κ * |α - sdpObjectiveMap C X₀|) * ‖u‖ := by
    rw [hgapIdentity]
    have hQle : sdpObjectiveMap C Q ≤ |sdpObjectiveMap C Q| := le_abs_self _
    have hcoeff :
        (κ * ‖u‖) * (α - sdpObjectiveMap C X₀) ≤
          κ * |α - sdpObjectiveMap C X₀| * ‖u‖ := by
      have habs : α - sdpObjectiveMap C X₀ ≤
          |α - sdpObjectiveMap C X₀| := le_abs_self _
      calc
        (κ * ‖u‖) * (α - sdpObjectiveMap C X₀)
            ≤ (κ * ‖u‖) * |α - sdpObjectiveMap C X₀| :=
              mul_le_mul_of_nonneg_left habs (mul_nonneg hκ.le (norm_nonneg u))
        _ = κ * |α - sdpObjectiveMap C X₀| * ‖u‖ := by ring
    nlinarith [hObjectiveQ]
  have hfinal :
      Matrix.trace (C * z.fst.1) - α * z.snd ≤ M * ‖u‖ := by
    have huNonneg : 0 ≤ ‖u‖ := norm_nonneg u
    calc
      Matrix.trace (C * z.fst.1) - α * z.snd ≤
          (‖sdpObjectiveMap C‖ * ‖constraintRangeRightInverse A‖ +
            κ * |α - sdpObjectiveMap C X₀|) * ‖u‖ := hgapBound
      _ ≤ M * ‖u‖ := by
            apply mul_le_mul_of_nonneg_right
            · dsimp [M]
              linarith
            · exact huNonneg
  have huNormLe : ‖uRaw‖ ≤ ‖WithLp.toLp 2 uRaw‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.toLp 2 uRaw))).2
    intro i
    exact PiLp.norm_apply_le (WithLp.toLp 2 uRaw) i
  have hfinalEuclidean :
      Matrix.trace (C * z.fst.1) - α * z.snd ≤
        M * ‖WithLp.toLp 2 uRaw‖ := by
    exact hfinal.trans (mul_le_mul_of_nonneg_left huNormLe hM.le)
  simpa [α, u, uRaw] using hfinalEuclidean

/-- Helper for Theorem 10.1: the closed homogenized primal cone image excludes the unit gap
point. -/
lemma gapPoint_notIn_primalHomogenizedConeMapL2
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hstrict : sdp_primal_strictly_feasible A b)
    (hbounded : BddAbove (sdp_primal_objective_values A b C)) :
    WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin m)), (1 : ℝ)) ∉
      (symmPsdScalarProperConeL2 n).map
        (primalHomogenizedSdpMapL2 A b C
          (sSup (sdp_primal_objective_values A b C))) := by
  obtain ⟨M, hM, hgap⟩ :=
    primalGap_le_constraintResidualNorm A b C hstrict hbounded
  let S : Set (WithLp 2 (EuclideanSpace ℝ (Fin m) × ℝ)) :=
    {w | w.snd ≤ M * ‖w.fst‖}
  have hSclosed : IsClosed S := by
    -- The quantitative epigraph is closed because both coordinate functions are continuous.
    exact isClosed_le
      (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin m)) ℝ).continuous
      ((continuous_const.mul
        (WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin m)) ℝ).continuous.norm))
  have himage :
      ((symmPsdScalarProperConeL2 n).toPointedCone.map
          ((primalHomogenizedSdpMapL2 A b C
            (sSup (sdp_primal_objective_values A b C)) :
              WithLp 2 (SymmMat n × ℝ) →ₗ[ℝ]
                WithLp 2 (EuclideanSpace ℝ (Fin m) × ℝ))) :
        Set (WithLp 2 (EuclideanSpace ℝ (Fin m) × ℝ))) ⊆ S := by
    rintro w ⟨z, hz, rfl⟩
    have hz' : z ∈ symmPsdScalarProperConeL2 n := hz
    have hbound := hgap z hz'
    simpa [S, primalHomogenizedSdpMapL2_apply] using hbound
  intro hmem
  have hclosure :
      WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin m)), (1 : ℝ)) ∈ S := by
    apply closure_minimal himage hSclosed
    exact (ProperCone.mem_map.mp hmem)
  have hone : (1 : ℝ) ≤ 0 := by simpa [S] using hclosure
  exact (not_le_of_gt zero_lt_one) hone

/-- Helper for Theorem 10.1: nonnegativity of a primal homogenized separator on the cone makes
its matrix coefficient positive semidefinite. -/
lemma primalSeparatorMatrixPosSemidef
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (α : ℝ) (p : WithLp 2 (EuclideanSpace ℝ (Fin m) × ℝ))
    (hseparator : ∀ z : WithLp 2 (SymmMat n × ℝ),
      z ∈ symmPsdScalarProperConeL2 n →
        0 ≤ inner ℝ (primalHomogenizedSdpMapL2 A b C α z) p) :
    ((∑ i, p.fst i • A i) + p.snd • C).PosSemidef := by
  have hLsymm : ((∑ i, p.fst i • A i) + p.snd • C).IsSymm :=
    linearCombination_isSymm A C hA hC p.fst p.snd
  let L : SymmMat n := ⟨(∑ i, p.fst i • A i) + p.snd • C, hLsymm⟩
  -- Rank-one tests of the cone separator are precisely the quadratic forms of `L`.
  have hLpsd : L.1.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.IsHermitian.ext fun i j ↦ by simpa using L.2.apply i j
    · intro u
      have htestMem :
          WithLp.toLp 2 (rankOneSymmGenerator u, (0 : ℝ)) ∈
            symmPsdScalarProperConeL2 n := by
        exact (mem_symmPsdScalarProperConeL2_iff
          (rankOneSymmGenerator u) 0).2
            ⟨(Matrix.posSemidef_vecMulVec_self_star u), le_rfl⟩
      have htest := hseparator
        (WithLp.toLp 2 (rankOneSymmGenerator u, (0 : ℝ))) htestMem
      have htest' :
          0 ≤ ∑ i, Matrix.trace (A i * Matrix.vecMulVec u u) * p.fst i +
            Matrix.trace (C * Matrix.vecMulVec u u) * p.snd := by
        simpa [primalHomogenizedSdpMapL2_apply,
          WithLp.prod_inner_apply, PiLp.inner_apply, mul_comm] using htest
      calc
        0 ≤ ∑ i, Matrix.trace (A i * Matrix.vecMulVec u u) * p.fst i +
            Matrix.trace (C * Matrix.vecMulVec u u) * p.snd := htest'
        _ = Matrix.trace (L.1 * Matrix.vecMulVec u u) := by
              have hsum :
                  (∑ i, Matrix.trace (A i * Matrix.vecMulVec u u) * p.fst i) =
                    ∑ i, p.fst i * Matrix.trace (A i * Matrix.vecMulVec u u) :=
                Finset.sum_congr rfl fun i _ ↦
                  mul_comm (Matrix.trace (A i * Matrix.vecMulVec u u)) (p.fst i)
              rw [hsum, mul_comm (Matrix.trace (C * Matrix.vecMulVec u u))]
              simp [L, Matrix.add_mul, Finset.sum_mul, Matrix.trace_add, Matrix.trace_sum,
                Matrix.trace_smul]
        _ = u ⬝ᵥ (L.1 *ᵥ u) :=
              trace_mul_rankOneSymmGenerator_eq_dotProduct_mulVec u L
  simpa [L] using hLpsd

/-- Helper for Theorem 10.1: testing a primal homogenized separator in the pure scale direction
gives its scalar objective inequality. -/
lemma primalSeparatorScalarInequality
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (p : WithLp 2 (EuclideanSpace ℝ (Fin m) × ℝ))
    (hseparator : ∀ z : WithLp 2 (SymmMat n × ℝ),
      z ∈ symmPsdScalarProperConeL2 n →
        0 ≤ inner ℝ (primalHomogenizedSdpMapL2 A b C α z) p) :
    sdp_dual_objective b p.fst + α * p.snd ≤ 0 := by
  have htestMem :
      WithLp.toLp 2 ((0 : SymmMat n), (1 : ℝ)) ∈
        symmPsdScalarProperConeL2 n := by
    exact (mem_symmPsdScalarProperConeL2_iff (0 : SymmMat n) 1).2
      ⟨(Matrix.PosSemidef.zero), zero_le_one⟩
  have htest := hseparator
    (WithLp.toLp 2 ((0 : SymmMat n), (1 : ℝ))) htestMem
  have hraw : p.snd * α ≤ -∑ i, p.fst i * b i := by
    simpa [primalHomogenizedSdpMapL2_apply, WithLp.prod_inner_apply,
      PiLp.inner_apply, sdp_dual_objective, Finset.sum_neg_distrib] using htest
  have hneg : 0 ≤ -(sdp_dual_objective b p.fst + α * p.snd) := by
    dsimp [sdp_dual_objective]
    nlinarith
  linarith

/-- Helper for Theorem 10.1: a separator with negative scalar coordinate normalizes to a
dual-feasible witness attaining the primal supremum. -/
lemma normalizePrimalSeparatorToDualCertificate
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hstrict : sdp_primal_strictly_feasible A b)
    {y : Fin m → ℝ} {μ : ℝ} (hμNeg : μ < 0)
    (hLpsd : ((∑ i, y i • A i) + μ • C).PosSemidef)
    (hscalar : sdp_dual_objective b y +
      sSup (sdp_primal_objective_values A b C) * μ ≤ 0) :
    ∃ y' : Fin m → ℝ,
      y' ∈ sdp_dual_feasible_region A C ∧
        sdp_dual_objective b y' = sSup (sdp_primal_objective_values A b C) := by
  let y' : Fin m → ℝ := (-μ)⁻¹ • y
  have hscalePos : 0 < -μ := neg_pos.mpr hμNeg
  have hscaleEq :
      (-μ)⁻¹ • ((∑ i, y i • A i) + μ • C) = sdp_dual_slack A C y' := by
    rw [linearCombination_eq_negScale_dualSlack A C y μ (ne_of_lt hμNeg)]
    simp only [y', inv_neg, neg_smul, smul_neg, smul_smul]
    rw [neg_mul, inv_mul_cancel₀ (ne_of_lt hμNeg), neg_smul, one_smul, neg_neg]
  have hy' : y' ∈ sdp_dual_feasible_region A C := by
    have hscaled := hLpsd.smul (inv_nonneg.mpr hscalePos.le)
    rw [hscaleEq] at hscaled
    exact hscaled
  have hobjUpper :
      sdp_dual_objective b y' ≤ sSup (sdp_primal_objective_values A b C) := by
    have hyBound : sdp_dual_objective b y ≤
        sSup (sdp_primal_objective_values A b C) * (-μ) := by
      linarith
    have hdiv : sdp_dual_objective b y / (-μ) ≤
        sSup (sdp_primal_objective_values A b C) :=
      (div_le_iff₀ hscalePos).2 (by simpa [mul_comm] using hyBound)
    simpa only [y', sdpDualObjective_smul, div_eq_mul_inv, mul_comm] using hdiv
  have hobjLower :
      sSup (sdp_primal_objective_values A b C) ≤ sdp_dual_objective b y' := by
    exact csSup_primalValues_le_dualObjective_of_dualFeasible A b C hstrict hy'
  -- The separator bound and weak duality meet at the primal supremum.
  exact ⟨y', hy', le_antisymm hobjUpper hobjLower⟩

/-- Helper for Theorem 10.1: under primal strict feasibility and bounded primal objective values,
the dual objective attains the primal supremum. -/
lemma sdpDualOptimalCertificateAtPrimalSup
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (hstrict : sdp_primal_strictly_feasible A b)
    (hbounded : BddAbove (sdp_primal_objective_values A b C)) :
    ∃ y : Fin m → ℝ,
      y ∈ sdp_dual_feasible_region A C ∧
        sdp_dual_objective b y = sSup (sdp_primal_objective_values A b C) := by
  let α := sSup (sdp_primal_objective_values A b C)
  let f := primalHomogenizedSdpMapL2 A b C α
  let gap : WithLp 2 (EuclideanSpace ℝ (Fin m) × ℝ) :=
    WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin m)), (1 : ℝ))
  have hgapNotMem : gap ∉ (symmPsdScalarProperConeL2 n).map f := by
    simpa [f, gap, α] using
      gapPoint_notIn_primalHomogenizedConeMapL2 A b C hstrict hbounded
  obtain ⟨p, hpAdjoint, hpGap⟩ :=
    (symmPsdScalarProperConeL2 n).hyperplane_separation_of_notMem hgapNotMem
  have hμNeg : p.snd < 0 := by
    -- Pairing with the unit gap point reads off the scalar separator coordinate.
    simpa [gap, WithLp.prod_inner_apply] using hpGap
  have hseparatorNonneg :
      ∀ z : WithLp 2 (SymmMat n × ℝ),
        z ∈ symmPsdScalarProperConeL2 n → 0 ≤ inner ℝ (f z) p := by
    intro z hz
    have hzInner := (ProperCone.mem_innerDual.mp hpAdjoint) hz
    rw [ContinuousLinearMap.adjoint_inner_right] at hzInner
    exact hzInner
  have hseparatorNonneg' :
      ∀ z : WithLp 2 (SymmMat n × ℝ),
        z ∈ symmPsdScalarProperConeL2 n →
          0 ≤ inner ℝ (primalHomogenizedSdpMapL2 A b C α z) p := by
    simpa [f] using hseparatorNonneg
  have hLpsd : ((∑ i, p.fst i • A i) + p.snd • C).PosSemidef :=
    primalSeparatorMatrixPosSemidef A b C hA hC α p hseparatorNonneg'
  have hscalar : sdp_dual_objective b p.fst + α * p.snd ≤ 0 :=
    primalSeparatorScalarInequality A b C α p hseparatorNonneg'
  -- Normalize the negative scalar coordinate to obtain the dual optimizer.
  exact normalizePrimalSeparatorToDualCertificate A b C hstrict hμNeg hLpsd hscalar

/-- Helper for Theorem 10.1: a symmetric constraint matrix regarded as an element of the
symmetric-matrix Hilbert space. -/
def symmetricConstraintMatrix
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsSymm)
    (i : Fin m) : SymmMat n :=
  ⟨A i, hA i⟩

/-- Helper for Theorem 10.1: the objective matrix regarded as an element of the symmetric-matrix
Hilbert space. -/
def symmetricObjectiveMatrix
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm) : SymmMat n :=
  ⟨C, hC⟩

/-- Helper for Theorem 10.1: the dual linear-combination operator from Euclidean coordinates to
symmetric matrices. -/
noncomputable def dualLinearCombinationMap
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsSymm) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] SymmMat n :=
  ∑ i, (EuclideanSpace.proj i).smulRight (symmetricConstraintMatrix A hA i)

/-- Helper for Theorem 10.1: evaluation of the dual linear-combination operator is the expected
finite matrix sum. -/
lemma dualLinearCombinationMap_apply
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsSymm)
    (y : EuclideanSpace ℝ (Fin m)) :
    (dualLinearCombinationMap A hA y).1 = ∑ i, y i • A i := by
  -- Evaluate each coordinate functional before forgetting the symmetric-subspace wrapper.
  simp [dualLinearCombinationMap, symmetricConstraintMatrix]

/-- Helper for Theorem 10.1: the dual objective as a continuous functional on Euclidean
coordinates. -/
noncomputable def dualObjectiveEuclideanMap
    (b : Fin m → ℝ) : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
  ∑ i, (EuclideanSpace.proj i).smulRight (b i)

/-- Helper for Theorem 10.1: the Euclidean objective functional agrees with the textbook dual
objective. -/
lemma dualObjectiveEuclideanMap_apply
    (b : Fin m → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    dualObjectiveEuclideanMap b y = sdp_dual_objective b y := by
  -- Expand the finite sum of coordinate functionals and commute scalar multiplication in `ℝ`.
  simp [dualObjectiveEuclideanMap, sdp_dual_objective, mul_comm]

/-- Helper for Theorem 10.1: the Hilbert domain for the dual homogenized cone, with PSD matrix,
scale, and unrestricted dual-vector coordinates. -/
abbrev DualHomogenizedDomain (m n : ℕ) :=
  WithLp 2 (WithLp 2 (SymmMat n × ℝ) × EuclideanSpace ℝ (Fin m))

/-- Helper for Theorem 10.1: the dual homogenized domain cone constrains only the matrix and scale
coordinates, leaving the dual vector unrestricted. -/
noncomputable def dualHomogenizedProperConeL2 (m n : ℕ) :
    ProperCone ℝ (DualHomogenizedDomain m n) :=
  (symmPsdScalarProperConeL2 n).comap
    (WithLp.fstL 2 ℝ (WithLp 2 (SymmMat n × ℝ)) (EuclideanSpace ℝ (Fin m)))

/-- Helper for Theorem 10.1: membership in the dual homogenized cone means PSD matrix and
nonnegative scale, with no condition on the vector coordinate. -/
lemma mem_dualHomogenizedProperConeL2_iff
    (z : DualHomogenizedDomain m n) :
    z ∈ dualHomogenizedProperConeL2 m n ↔
      z.fst.fst.1.PosSemidef ∧ 0 ≤ z.fst.snd := by
  -- The cone is a direct comap of the already characterized PSD-and-scale cone.
  exact mem_symmPsdScalarProperConeL2_iff z.fst.fst z.fst.snd

/-- Helper for Theorem 10.1: the matrix residual of a homogenized dual point. -/
noncomputable def dualHomogenizedResidualMap
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) :
    DualHomogenizedDomain m n →L[ℝ] SymmMat n :=
  let fstOuter :=
    WithLp.fstL 2 ℝ (WithLp 2 (SymmMat n × ℝ)) (EuclideanSpace ℝ (Fin m))
  let sndOuter :=
    WithLp.sndL 2 ℝ (WithLp 2 (SymmMat n × ℝ)) (EuclideanSpace ℝ (Fin m))
  let matrixCoord := (WithLp.fstL 2 ℝ (SymmMat n) ℝ).comp fstOuter
  let scaleCoord := (WithLp.sndL 2 ℝ (SymmMat n) ℝ).comp fstOuter
  matrixCoord - (dualLinearCombinationMap A hA).comp sndOuter +
    scaleCoord.smulRight (symmetricObjectiveMatrix C hC)

/-- Helper for Theorem 10.1: the scalar residual records the gap from the candidate dual
infimum. -/
noncomputable def dualHomogenizedGapMap
    (b : Fin m → ℝ) (β : ℝ) :
    DualHomogenizedDomain m n →L[ℝ] ℝ :=
  let fstOuter :=
    WithLp.fstL 2 ℝ (WithLp 2 (SymmMat n × ℝ)) (EuclideanSpace ℝ (Fin m))
  let sndOuter :=
    WithLp.sndL 2 ℝ (WithLp 2 (SymmMat n × ℝ)) (EuclideanSpace ℝ (Fin m))
  let scaleCoord := (WithLp.sndL 2 ℝ (SymmMat n) ℝ).comp fstOuter
  β • scaleCoord - (dualObjectiveEuclideanMap b).comp sndOuter

/-- Helper for Theorem 10.1: the dual homogenized map pairs its symmetric-matrix residual with
its scalar objective gap. -/
noncomputable def dualHomogenizedSdpMapL2
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) (β : ℝ) :
    DualHomogenizedDomain m n →L[ℝ] WithLp 2 (SymmMat n × ℝ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (SymmMat n) ℝ).symm :
      (SymmMat n × ℝ) →L[ℝ] WithLp 2 (SymmMat n × ℝ)) ∘L
    (dualHomogenizedResidualMap A C hA hC).prod
      (dualHomogenizedGapMap b β)

/-- Helper for Theorem 10.1: evaluating the dual homogenized map exposes the slack residual and
objective gap coordinates. -/
lemma dualHomogenizedSdpMapL2_apply
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) (β : ℝ)
    (z : DualHomogenizedDomain m n) :
    dualHomogenizedSdpMapL2 A b C hA hC β z =
      WithLp.toLp 2
        (z.fst.fst - dualLinearCombinationMap A hA z.snd +
            z.fst.snd • symmetricObjectiveMatrix C hC,
          β * z.fst.snd - sdp_dual_objective b z.snd) := by
  -- Unfold only the continuous-map interface and then use the two coordinate computation rules.
  simp [dualHomogenizedSdpMapL2, dualHomogenizedResidualMap,
    dualHomogenizedGapMap, dualObjectiveEuclideanMap_apply]

/-- Helper for Theorem 10.1: an exact homogenized dual point cannot have positive gap above the
dual infimum. -/
lemma dualGap_nonpos_of_exactResidual
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hstrict : sdp_dual_strictly_feasible A C)
    (hbounded : BddBelow (sdp_dual_objective_values A b C))
    {S : SymmMat n} {τ : ℝ} {y : EuclideanSpace ℝ (Fin m)}
    (hS : S.1.PosSemidef) (hτ : 0 ≤ τ)
    (hres : S.1 = (∑ i, y i • A i) - τ • C) :
    sInf (sdp_dual_objective_values A b C) * τ - sdp_dual_objective b y ≤ 0 := by
  let β := sInf (sdp_dual_objective_values A b C)
  by_cases hτzero : τ = 0
  · have hobjNonneg : 0 ≤ sdp_dual_objective b y := by
      by_contra hobj
      have hobjNeg : sdp_dual_objective b y < 0 := lt_of_not_ge hobj
      rcases sdp_dual_strictly_feasible.exists_mem_dual_feasible_region A C hstrict with
        ⟨y₀, hy₀, _⟩
      rcases hbounded with ⟨M, hM⟩
      obtain ⟨k, hk⟩ :=
        exists_nat_gt ((sdp_dual_objective b y₀ - M) / (-sdp_dual_objective b y))
      have hkReal :
          (sdp_dual_objective b y₀ - M) / (-sdp_dual_objective b y) < (k : ℝ) := by
        exact_mod_cast hk
      have hgrowth :
          sdp_dual_objective b y₀ - M <
            (k : ℝ) * (-sdp_dual_objective b y) := by
        exact (div_lt_iff₀ (neg_pos.mpr hobjNeg)).mp hkReal
      let yk : Fin m → ℝ := y₀ + (k : ℝ) • y
      have hslackEq :
          sdp_dual_slack A C yk =
            sdp_dual_slack A C y₀ + (k : ℝ) • S.1 := by
        calc
          sdp_dual_slack A C yk =
              (∑ i, y₀ i • A i) + (k : ℝ) • (∑ i, y i • A i) - C := by
                simp [sdp_dual_slack, yk, Finset.sum_add_distrib,
                  Finset.smul_sum, smul_smul, add_smul]
          _ = sdp_dual_slack A C y₀ + (k : ℝ) • S.1 := by
                rw [hres, hτzero]
                simp [sdp_dual_slack]
                abel
      have hyk : yk ∈ sdp_dual_feasible_region A C := by
        rw [mem_sdp_dual_feasible_region_iff, hslackEq]
        exact hy₀.add (hS.smul (by positivity))
      have hobjEq :
          sdp_dual_objective b yk =
            sdp_dual_objective b y₀ + (k : ℝ) * sdp_dual_objective b y := by
        calc
          sdp_dual_objective b yk =
              sdp_dual_objective b y₀ +
                sdp_dual_objective b ((k : ℝ) • y) := by
                  simp [sdp_dual_objective, yk, Finset.sum_add_distrib, add_mul]
          _ = sdp_dual_objective b y₀ +
                (k : ℝ) * sdp_dual_objective b y := by
                  rw [sdpDualObjective_smul]
      have hvalue : sdp_dual_objective b yk ∈ sdp_dual_objective_values A b C :=
        ⟨yk, hyk, rfl⟩
      have hlower : M ≤ sdp_dual_objective b yk := hM hvalue
      rw [hobjEq] at hlower
      linarith
    simpa [β, hτzero] using neg_nonpos.mpr hobjNonneg
  · have hτpos : 0 < τ := lt_of_le_of_ne hτ (by simpa [eq_comm] using hτzero)
    let y' : Fin m → ℝ := τ⁻¹ • y
    have hslackEq : sdp_dual_slack A C y' = τ⁻¹ • S.1 := by
      rw [hres]
      ext i j
      simp only [sdp_dual_slack, y', Matrix.smul_apply, Matrix.sub_apply,
        Matrix.sum_apply, smul_eq_mul]
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro k hk
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      · field_simp [hτzero]
    have hy' : y' ∈ sdp_dual_feasible_region A C := by
      rw [mem_sdp_dual_feasible_region_iff, hslackEq]
      exact hS.smul (inv_nonneg.mpr hτ)
    have hvalue : sdp_dual_objective b y' ∈ sdp_dual_objective_values A b C :=
      ⟨y', hy', rfl⟩
    have hβ : β ≤ sdp_dual_objective b y' := csInf_le hbounded hvalue
    have hobjEq :
        sdp_dual_objective b y' = τ⁻¹ * sdp_dual_objective b y := by
      exact sdpDualObjective_smul b τ⁻¹ y
    rw [hobjEq] at hβ
    have hscaled : β * τ ≤ sdp_dual_objective b y := by
      exact (le_div_iff₀ hτpos).mp (by simpa [div_eq_mul_inv, mul_comm] using hβ)
    simpa [β, sub_nonpos] using hscaled

/-- Helper for Theorem 10.1: on the homogenized dual cone, the objective gap is bounded by a
fixed multiple of the symmetric residual norm. -/
lemma dualGap_le_residualNorm
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (hstrict : sdp_dual_strictly_feasible A C)
    (hbounded : BddBelow (sdp_dual_objective_values A b C)) :
    ∃ M : ℝ, 0 < M ∧
      ∀ z : DualHomogenizedDomain m n,
        z ∈ dualHomogenizedProperConeL2 m n →
          sInf (sdp_dual_objective_values A b C) * z.fst.snd -
              sdp_dual_objective b z.snd ≤
            M * ‖z.fst.fst - dualLinearCombinationMap A hA z.snd +
              z.fst.snd • symmetricObjectiveMatrix C hC‖ := by
  rcases sdp_dual_strictly_feasible.exists_mem_dual_feasible_region A C hstrict with
    ⟨y₀, _, hy₀pd⟩
  let y₀L : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 y₀
  let S₀ : SymmMat n := ⟨sdp_dual_slack A C y₀, sdpDualSlack_isSymm A C hA hC y₀⟩
  obtain ⟨κ, hκ, hcorrection⟩ :=
    scaledStrictWitnessCorrectionPosSemidef
      (ContinuousLinearMap.id ℝ (SymmMat n)) S₀ hy₀pd
  let β := sInf (sdp_dual_objective_values A b C)
  let M : ℝ := κ * |sdp_dual_objective b y₀ - β| + 1
  have hM : 0 < M := by
    dsimp [M]
    have := mul_nonneg hκ.le (abs_nonneg (sdp_dual_objective b y₀ - β))
    linarith
  refine ⟨M, hM, ?_⟩
  intro z hz
  have hzMem : z.fst.fst.1.PosSemidef ∧ 0 ≤ z.fst.snd :=
    (mem_dualHomogenizedProperConeL2_iff z).1 hz
  let e : SymmMat n :=
    z.fst.fst - dualLinearCombinationMap A hA z.snd +
      z.fst.snd • symmetricObjectiveMatrix C hC
  let a : ℝ := κ * ‖e‖
  let D : SymmMat n := a • S₀ - e
  have hD : D.1.PosSemidef := by
    simpa [D, a] using hcorrection e
  let S' : SymmMat n := z.fst.fst + D
  let τ' : ℝ := z.fst.snd + a
  let y' : EuclideanSpace ℝ (Fin m) := z.snd + a • y₀L
  have hS' : S'.1.PosSemidef := hzMem.1.add hD
  have hτ' : 0 ≤ τ' := by
    exact add_nonneg hzMem.2 (mul_nonneg hκ.le (norm_nonneg e))
  have hS₀Eq :
      S₀ = dualLinearCombinationMap A hA y₀L - symmetricObjectiveMatrix C hC := by
    ext i j
    simp [S₀, y₀L, sdp_dual_slack, dualLinearCombinationMap_apply,
      symmetricObjectiveMatrix]
  have hexactSymm :
      S' = dualLinearCombinationMap A hA y' -
        τ' • symmetricObjectiveMatrix C hC := by
    simp [S', D, e, y', τ', hS₀Eq]
    module
  have hexact : S'.1 = (∑ i, y' i • A i) - τ' • C := by
    have := congrArg Subtype.val hexactSymm
    simpa [dualLinearCombinationMap_apply, symmetricObjectiveMatrix] using this
  have hcorrectedGap : β * τ' - sdp_dual_objective b y' ≤ 0 := by
    simpa [β] using
      dualGap_nonpos_of_exactResidual A b C hstrict hbounded hS' hτ' hexact
  have hyObj :
      sdp_dual_objective b y' =
        sdp_dual_objective b z.snd + a * sdp_dual_objective b y₀ := by
    calc
      sdp_dual_objective b y' = dualObjectiveEuclideanMap b y' := by
        rw [dualObjectiveEuclideanMap_apply]
      _ = dualObjectiveEuclideanMap b z.snd +
          a * dualObjectiveEuclideanMap b y₀L := by
            simp [y']
      _ = sdp_dual_objective b z.snd + a * sdp_dual_objective b y₀ := by
            simp [dualObjectiveEuclideanMap_apply, y₀L]
  have hgapIdentity :
      β * z.fst.snd - sdp_dual_objective b z.snd =
        (β * τ' - sdp_dual_objective b y') +
          a * (sdp_dual_objective b y₀ - β) := by
    rw [hyObj]
    simp [τ']
    ring
  have hgapBound :
      β * z.fst.snd - sdp_dual_objective b z.snd ≤
        κ * |sdp_dual_objective b y₀ - β| * ‖e‖ := by
    rw [hgapIdentity]
    have habs : sdp_dual_objective b y₀ - β ≤
        |sdp_dual_objective b y₀ - β| := le_abs_self _
    have haNonneg : 0 ≤ a := mul_nonneg hκ.le (norm_nonneg e)
    calc
      (β * τ' - sdp_dual_objective b y') +
          a * (sdp_dual_objective b y₀ - β)
          ≤ a * (sdp_dual_objective b y₀ - β) := by linarith
      _ ≤ a * |sdp_dual_objective b y₀ - β| :=
        mul_le_mul_of_nonneg_left habs haNonneg
      _ = κ * |sdp_dual_objective b y₀ - β| * ‖e‖ := by
        simp [a]
        ring
  have hfinal :
      β * z.fst.snd - sdp_dual_objective b z.snd ≤ M * ‖e‖ := by
    exact hgapBound.trans (mul_le_mul_of_nonneg_right (by dsimp [M]; linarith) (norm_nonneg e))
  simpa [β, e] using hfinal

/-- Helper for Theorem 10.1: the closed homogenized dual cone image excludes the unit gap
point. -/
lemma gapPoint_notIn_dualHomogenizedConeMapL2
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (hstrict : sdp_dual_strictly_feasible A C)
    (hbounded : BddBelow (sdp_dual_objective_values A b C)) :
    WithLp.toLp 2 ((0 : SymmMat n), (1 : ℝ)) ∉
      (dualHomogenizedProperConeL2 m n).map
        (dualHomogenizedSdpMapL2 A b C hA hC
          (sInf (sdp_dual_objective_values A b C))) := by
  obtain ⟨M, hM, hgap⟩ :=
    dualGap_le_residualNorm A b C hA hC hstrict hbounded
  let T : Set (WithLp 2 (SymmMat n × ℝ)) := {w | w.snd ≤ M * ‖w.fst‖}
  have hTclosed : IsClosed T := by
    -- The norm epigraph containing the exact image is closed.
    exact isClosed_le
      (WithLp.sndL 2 ℝ (SymmMat n) ℝ).continuous
      (continuous_const.mul (WithLp.fstL 2 ℝ (SymmMat n) ℝ).continuous.norm)
  have himage :
      ((dualHomogenizedProperConeL2 m n).toPointedCone.map
          ((dualHomogenizedSdpMapL2 A b C hA hC
            (sInf (sdp_dual_objective_values A b C)) :
              DualHomogenizedDomain m n →ₗ[ℝ] WithLp 2 (SymmMat n × ℝ))) :
        Set (WithLp 2 (SymmMat n × ℝ))) ⊆ T := by
    rintro w ⟨z, hz, rfl⟩
    have hbound := hgap z hz
    simpa [T, dualHomogenizedSdpMapL2_apply] using hbound
  intro hmem
  have hclosure : WithLp.toLp 2 ((0 : SymmMat n), (1 : ℝ)) ∈ T := by
    apply closure_minimal himage hTclosed
    exact ProperCone.mem_map.mp hmem
  have hone : (1 : ℝ) ≤ 0 := by simpa [T] using hclosure
  exact (not_le_of_gt zero_lt_one) hone

/-- Helper for Theorem 10.1: nonnegativity of a dual homogenized separator on the cone makes
its matrix coordinate positive semidefinite. -/
lemma dualSeparatorMatrixPosSemidef
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) (β : ℝ)
    (p : WithLp 2 (SymmMat n × ℝ))
    (hseparator : ∀ z : DualHomogenizedDomain m n,
      z ∈ dualHomogenizedProperConeL2 m n →
        0 ≤ inner ℝ (dualHomogenizedSdpMapL2 A b C hA hC β z) p) :
    p.fst.1.PosSemidef := by
  -- Rank-one tests of the separator are the quadratic forms of its matrix coordinate.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.ext fun i j ↦ by simpa using p.fst.2.apply i j
  · intro u
    let z : DualHomogenizedDomain m n :=
      WithLp.toLp 2
        (WithLp.toLp 2 (rankOneSymmGenerator u, (0 : ℝ)),
          (0 : EuclideanSpace ℝ (Fin m)))
    have hz : z ∈ dualHomogenizedProperConeL2 m n := by
      exact (mem_dualHomogenizedProperConeL2_iff z).2
        ⟨Matrix.posSemidef_vecMulVec_self_star u, le_rfl⟩
    have htest := hseparator z hz
    have hinner : 0 ≤ inner ℝ (rankOneSymmGenerator u) p.fst := by
      simpa [z, dualHomogenizedSdpMapL2_apply, WithLp.prod_inner_apply,
        sdp_dual_objective] using htest
    rw [rankOneSymmGenerator_inner_eq_dotProduct_mulVec] at hinner
    exact hinner

/-- Helper for Theorem 10.1: the unrestricted vector directions force the matrix separator to
satisfy the primal trace constraints after normalization. -/
lemma dualSeparatorConstraintEquation
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) (β : ℝ)
    (p : WithLp 2 (SymmMat n × ℝ))
    (hseparator : ∀ z : DualHomogenizedDomain m n,
      z ∈ dualHomogenizedProperConeL2 m n →
        0 ≤ inner ℝ (dualHomogenizedSdpMapL2 A b C hA hC β z) p) :
    ∀ i, Matrix.trace (A i * p.fst.1) = (-p.snd) * b i := by
  intro i
  let e : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (Pi.single i (1 : ℝ))
  let z : DualHomogenizedDomain m n :=
    WithLp.toLp 2 (WithLp.toLp 2 ((0 : SymmMat n), (0 : ℝ)), e)
  have hz : z ∈ dualHomogenizedProperConeL2 m n := by
    exact (mem_dualHomogenizedProperConeL2_iff z).2
      ⟨Matrix.PosSemidef.zero, le_rfl⟩
  have hnegz : -z ∈ dualHomogenizedProperConeL2 m n := by
    apply (mem_dualHomogenizedProperConeL2_iff (-z)).2
    simpa [z] using
      (And.intro (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef) (le_rfl : (0 : ℝ) ≤ 0))
  have hforward := hseparator z hz
  have hbackward := hseparator (-z) hnegz
  have hzero : inner ℝ (dualHomogenizedSdpMapL2 A b C hA hC β z) p = 0 := by
    rw [map_neg, inner_neg_left] at hbackward
    linarith
  have hLinearCombination :
      dualLinearCombinationMap A hA e = symmetricConstraintMatrix A hA i := by
    ext r s
    simp [e, dualLinearCombinationMap_apply, symmetricConstraintMatrix]
  have hObjective : sdp_dual_objective b e = b i := by
    simp [e, sdp_dual_objective, Pi.single_apply]
  have hmap :
      dualHomogenizedSdpMapL2 A b C hA hC β z =
        WithLp.toLp 2 (-symmetricConstraintMatrix A hA i, -b i) := by
    simp [z, dualHomogenizedSdpMapL2_apply, hLinearCombination, hObjective]
  -- Evaluating the vanishing functional on a coordinate basis vector gives one constraint.
  rw [hmap, WithLp.prod_inner_apply, inner_neg_left,
    inner_symmMat_eq_trace_mul] at hzero
  dsimp [symmetricConstraintMatrix] at hzero
  rw [Matrix.trace_mul_comm] at hzero
  simp at hzero
  linarith

/-- Helper for Theorem 10.1: testing a dual homogenized separator in the pure scale direction
gives the lower objective inequality used to normalize the primal witness. -/
lemma dualSeparatorObjectiveInequality
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) (β : ℝ)
    (p : WithLp 2 (SymmMat n × ℝ))
    (hseparator : ∀ z : DualHomogenizedDomain m n,
      z ∈ dualHomogenizedProperConeL2 m n →
        0 ≤ inner ℝ (dualHomogenizedSdpMapL2 A b C hA hC β z) p) :
    0 ≤ Matrix.trace (C * p.fst.1) + β * p.snd := by
  let z : DualHomogenizedDomain m n :=
    WithLp.toLp 2
      (WithLp.toLp 2 ((0 : SymmMat n), (1 : ℝ)),
        (0 : EuclideanSpace ℝ (Fin m)))
  have hz : z ∈ dualHomogenizedProperConeL2 m n := by
    exact (mem_dualHomogenizedProperConeL2_iff z).2
      ⟨Matrix.PosSemidef.zero, zero_le_one⟩
  have htest := hseparator z hz
  have hmap :
      dualHomogenizedSdpMapL2 A b C hA hC β z =
        WithLp.toLp 2 (symmetricObjectiveMatrix C hC, β) := by
    simp [z, dualHomogenizedSdpMapL2_apply, sdp_dual_objective]
  -- The scale ray contributes exactly the objective matrix and the candidate infimum.
  rw [hmap, WithLp.prod_inner_apply, inner_symmMat_eq_trace_mul] at htest
  dsimp [symmetricObjectiveMatrix] at htest
  rw [Matrix.trace_mul_comm] at htest
  simp at htest
  nlinarith

/-- Helper for Theorem 10.1: under dual strict feasibility and bounded dual objective values, the
primal objective attains the dual infimum. -/
lemma sdpPrimalOptimalCertificateAtDualInf
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (hstrict : sdp_dual_strictly_feasible A C)
    (hbounded : BddBelow (sdp_dual_objective_values A b C)) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X ∈ sdp_primal_feasible_region A b ∧
        sdp_primal_objective C X = sInf (sdp_dual_objective_values A b C) := by
  let β := sInf (sdp_dual_objective_values A b C)
  let f := dualHomogenizedSdpMapL2 A b C hA hC β
  let gap : WithLp 2 (SymmMat n × ℝ) :=
    WithLp.toLp 2 ((0 : SymmMat n), (1 : ℝ))
  have hboundAgainstAnyPrimal :
      ∀ X : Matrix (Fin n) (Fin n) ℝ,
        X ∈ sdp_primal_feasible_region A b → sdp_primal_objective C X ≤ β := by
    intro X hX
    exact primalObjective_le_csInf_dualValues_of_primalFeasible A b C hstrict hX
  have hgapNotMem : gap ∉ (dualHomogenizedProperConeL2 m n).map f := by
    -- The quantitative residual bound already excludes the unit gap from the closed cone image.
    simpa [f, gap, β] using
      gapPoint_notIn_dualHomogenizedConeMapL2 A b C hA hC hstrict hbounded
  obtain ⟨p, hpAdjoint, hpGap⟩ :=
    (dualHomogenizedProperConeL2 m n).hyperplane_separation_of_notMem hgapNotMem
  have hμNeg : p.snd < 0 := by
    -- Pairing the separator with the unit gap reads off its scalar coordinate.
    simpa [gap, WithLp.prod_inner_apply] using hpGap
  have hseparatorNonneg :
      ∀ z : DualHomogenizedDomain m n,
        z ∈ dualHomogenizedProperConeL2 m n → 0 ≤ inner ℝ (f z) p := by
    intro z hz
    have hzInner := (ProperCone.mem_innerDual.mp hpAdjoint) hz
    rw [ContinuousLinearMap.adjoint_inner_right] at hzInner
    exact hzInner
  have hseparatorNonneg' :
      ∀ z : DualHomogenizedDomain m n,
        z ∈ dualHomogenizedProperConeL2 m n →
          0 ≤ inner ℝ (dualHomogenizedSdpMapL2 A b C hA hC β z) p := by
    simpa [f] using hseparatorNonneg
  have hpPsd : p.fst.1.PosSemidef :=
    dualSeparatorMatrixPosSemidef A b C hA hC β p hseparatorNonneg'
  have hpConstraints :
      ∀ i, Matrix.trace (A i * p.fst.1) = (-p.snd) * b i :=
    dualSeparatorConstraintEquation A b C hA hC β p hseparatorNonneg'
  have hpObjective : 0 ≤ Matrix.trace (C * p.fst.1) + β * p.snd :=
    dualSeparatorObjectiveInequality A b C hA hC β p hseparatorNonneg'
  let X : Matrix (Fin n) (Fin n) ℝ := (-p.snd)⁻¹ • p.fst.1
  have hscalePos : 0 < -p.snd := neg_pos.mpr hμNeg
  have hμNe : p.snd ≠ 0 := ne_of_lt hμNeg
  have hXpsd : X.PosSemidef := by
    -- Positive scaling preserves the separator's positive semidefiniteness.
    simpa [X] using hpPsd.smul (inv_nonneg.mpr hscalePos.le)
  have hXconstraints : ∀ i, Matrix.trace (A i * X) = b i := by
    intro i
    -- The separator equations become the primal constraints after normalization.
    calc
      Matrix.trace (A i * X) =
          (-p.snd)⁻¹ * Matrix.trace (A i * p.fst.1) := by
            simp [X, Matrix.trace_smul, smul_eq_mul]
      _ = (-p.snd)⁻¹ * ((-p.snd) * b i) := by rw [hpConstraints i]
      _ = b i := by simp [hμNe]
  have hX : X ∈ sdp_primal_feasible_region A b := ⟨hXpsd, hXconstraints⟩
  have hobjScale : β * (-p.snd) ≤ Matrix.trace (C * p.fst.1) := by
    linarith
  have hobjLowerRaw : β ≤ Matrix.trace (C * p.fst.1) / (-p.snd) :=
    (le_div_iff₀ hscalePos).2 hobjScale
  have hobjLower : β ≤ sdp_primal_objective C X := by
    -- Divide the separator objective inequality by its positive normalization scale.
    simpa [sdp_primal_objective, X, Matrix.mul_smul, Matrix.trace_smul,
      div_eq_mul_inv, mul_comm, smul_eq_mul] using hobjLowerRaw
  have hobjUpper : sdp_primal_objective C X ≤ β :=
    hboundAgainstAnyPrimal X hX
  -- Weak duality and the normalized separator bound meet at the dual infimum.
  exact ⟨X, hX, le_antisymm hobjUpper hobjLower⟩

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap10/section_10_1/ch10_sec10_1_theorem_10_1.lean
Theorem 10.1 (1). If the primal semidefinite problem is strictly feasible and its objective
values are bounded above, then the dual problem admits an optimal solution and the primal and dual
optimal values coincide. -/
theorem sdp_dual_has_optimal_solution_of_primal_strict_feasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (hstrict : sdp_primal_strictly_feasible A b)
    (hbounded : BddAbove (sdp_primal_objective_values A b C)) :
    (∃ y : Fin m → ℝ,
      y ∈ sdp_dual_feasible_region A C ∧
        IsLeast (sdp_dual_objective_values A b C) (sdp_dual_objective b y)) ∧
      sSup (sdp_primal_objective_values A b C) = sInf (sdp_dual_objective_values A b C) := by
  rcases
      sdpDualOptimalCertificateAtPrimalSup A b C hA hC hstrict hbounded with
    ⟨y, hy, hyEq⟩
  have hprimalValuesNonempty : (sdp_primal_objective_values A b C).Nonempty := by
    rcases
        sdp_primal_strictly_feasible.exists_mem_primal_feasible_region A b hstrict with
      ⟨X, hX, _⟩
    exact ⟨sdp_primal_objective C X, ⟨X, hX, rfl⟩⟩
  have hyLeast :
      IsLeast (sdp_dual_objective_values A b C) (sdp_dual_objective b y) := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    intro r hr
    rcases (mem_sdp_dual_objective_values_iff A b C r).1 hr with ⟨u, hu, rfl⟩
    rw [hyEq]
    -- Every dual-feasible value bounds all primal-feasible objective values from above.
    refine csSup_le hprimalValuesNonempty ?_
    intro z hz
    rcases (mem_sdp_primal_objective_values_iff A b C z).1 hz with ⟨X, hX, rfl⟩
    exact sdpWeakDualityFeasiblePair A b C hX hu
  refine ⟨⟨y, hy, hyLeast⟩, ?_⟩
  -- The attained least dual value identifies the common optimum.
  calc
    sSup (sdp_primal_objective_values A b C) = sdp_dual_objective b y := hyEq.symm
    _ = sInf (sdp_dual_objective_values A b C) := hyLeast.csInf_eq.symm

/-- Theorem 10.1 (2). If the dual semidefinite problem is strictly feasible and its objective
values are bounded below, then the primal problem admits an optimal solution and the primal and
dual optimal values coincide. -/
theorem sdp_primal_has_optimal_solution_of_dual_strict_feasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (hstrict : sdp_dual_strictly_feasible A C)
    (hbounded : BddBelow (sdp_dual_objective_values A b C)) :
    (∃ X : Matrix (Fin n) (Fin n) ℝ,
      X ∈ sdp_primal_feasible_region A b ∧
        IsGreatest (sdp_primal_objective_values A b C) (sdp_primal_objective C X)) ∧
      sSup (sdp_primal_objective_values A b C) = sInf (sdp_dual_objective_values A b C) := by
  rcases
      sdpPrimalOptimalCertificateAtDualInf A b C hA hC hstrict hbounded with
    ⟨X, hX, hXEq⟩
  have hdualValuesNonempty : (sdp_dual_objective_values A b C).Nonempty := by
    rcases sdp_dual_strictly_feasible.exists_mem_dual_feasible_region A C hstrict with
      ⟨y, hy, _⟩
    exact ⟨sdp_dual_objective b y, ⟨y, hy, rfl⟩⟩
  have hXGreatest :
      IsGreatest (sdp_primal_objective_values A b C) (sdp_primal_objective C X) := by
    refine ⟨⟨X, hX, rfl⟩, ?_⟩
    intro r hr
    rcases (mem_sdp_primal_objective_values_iff A b C r).1 hr with ⟨Z, hZ, rfl⟩
    rw [hXEq]
    -- Every dual-feasible value bounds each primal-feasible value from above.
    refine le_csInf hdualValuesNonempty ?_
    intro w hw
    rcases (mem_sdp_dual_objective_values_iff A b C w).1 hw with ⟨y, hy, rfl⟩
    exact sdpWeakDualityFeasiblePair A b C hZ hy
  refine ⟨⟨X, hX, hXGreatest⟩, ?_⟩
  -- The attained greatest primal value is the same as the attained dual infimum.
  calc
    sSup (sdp_primal_objective_values A b C) = sdp_primal_objective C X := hXGreatest.csSup_eq
    _ = sInf (sdp_dual_objective_values A b C) := hXEq

/- Theorem 10.1 (3). The principal-submatrix statement is already the canonical mathlib theorem
`Matrix.PosSemidef.submatrix`, so this file recalls that owner directly instead of keeping a
parallel local wrapper. -/
recall Matrix.PosSemidef.submatrix

end Theorem101

#print axioms sdp_dual_has_optimal_solution_of_primal_strict_feasible
#print axioms sdp_primal_has_optimal_solution_of_dual_strict_feasible
