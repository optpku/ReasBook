/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace ConsensusADMM

universe u v

noncomputable section

open scoped MatrixOrder

namespace GramCycle

/-- The linear functional `G ↦ dotProduct z (G.mulVec w)` on real matrices. -/
def supportFunctional {ι : Type u} [Fintype ι] (z w : ι → ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
  (dotProductBilin ℝ ℝ z).comp ((Matrix.mulVecBilin ℝ ℝ).flip w)

/-- Evaluation of the matrix-linear Gram pairing. -/
theorem supportFunctional_apply {ι : Type u} [Fintype ι] (z w : ι → ℝ)
    (G : Matrix ι ι ℝ) :
    supportFunctional z w G = dotProduct z (G.mulVec w) := by
  -- Evaluate the two composed bilinear maps at the matrix argument.
  rfl

/-- The canonical Euclidean square-root realization map of a real Gram matrix. -/
def gramMap {ι : Type u} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) :
    (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap.comp
    (Matrix.mulVecLin (CFC.sqrt G))

/-- Evaluation of the canonical square-root realization map. -/
theorem gramMap_apply {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (z : ι → ℝ) :
    gramMap G z = WithLp.toLp 2 ((CFC.sqrt G).mulVec z) := by
  -- Evaluate the composite of the matrix action and the Euclidean-space equivalence.
  rfl

/-- The square-root realization converts the Euclidean pairing into the matrix Gram pairing. -/
theorem gramMap_inner {N : ℕ}
    (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) (hG : G.PosSemidef)
    (z w : (Fin 2 × Fin N) → ℝ) :
    dotProduct (gramMap G z) (gramMap G w) = supportFunctional z w G := by
  -- Positive semidefiniteness makes the square root symmetric and factors `G`.
  have gramSymm : G.IsSymm := Matrix.isHermitian_iff_isSymm.mp hG.isHermitian
  have sqrtFactor : (CFC.sqrt G).transpose * CFC.sqrt G = G := by
    have sqrtSymm : (CFC.sqrt G).IsSymm :=
      Matrix.isHermitian_iff_isSymm.mp
        (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)).isHermitian
    calc
      (CFC.sqrt G).transpose * CFC.sqrt G = CFC.sqrt G * CFC.sqrt G := by
        rw [sqrtSymm.eq]
      _ = G := CFC.sqrt_mul_sqrt_self G hG.nonneg
  -- Move one square-root factor across the dot product and collapse the factorization.
  rw [gramMap_apply, gramMap_apply, supportFunctional_apply]
  rw [Matrix.dotProduct_mulVec (v := (CFC.sqrt G).mulVec z)
    (A := CFC.sqrt G) (w := w)]
  rw [← Matrix.mulVec_transpose (A := CFC.sqrt G)
    (x := (CFC.sqrt G).mulVec z)]
  rw [Matrix.mulVec_mulVec, sqrtFactor]
  calc
    G.mulVec z ⬝ᵥ w = w ⬝ᵥ G.mulVec z := dotProduct_comm _ _
    _ = z ⬝ᵥ G.mulVec w := by
      simpa only [gramSymm.eq] using
        Matrix.dotProduct_transpose_mulVec (A := G) (x := w) (y := z)

/-- The real Euclidean inner product of realized vectors is their matrix Gram pairing. -/
private lemma gramMap_realInner {N : ℕ}
    (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) (hG : G.PosSemidef)
    (z w : (Fin 2 × Fin N) → ℝ) :
    inner ℝ (gramMap G z) (gramMap G w) = supportFunctional z w G := by
  -- Commute the real inner product so its coordinate dot product has the desired order.
  rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact gramMap_inner G hG z w

/-- A linear map carries a residual family to the residual family of the mapped data. -/
private lemma mapResidualFamily {N : ℕ} {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (γ : ℝ) (ν : ZMod N → E) :
    (fun i ↦ L (ProjectionCycle.residual γ ν i)) =
      ProjectionCycle.residual γ (fun i ↦ L (ν i)) := by
  -- Move the linear map through the residual's scalar multiple and difference.
  ext i
  rw [ProjectionCycle.residual_apply, ProjectionCycle.residual_apply,
    LinearMap.map_smul, LinearMap.map_sub]

/-- A linear map carries a first-vertex family to that of the mapped data. -/
private lemma mapXVertexFamily {N : ℕ} {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (γ : ℝ) (η ν : ZMod N → E) :
    (fun i ↦ L (ProjectionCycle.xVertex γ η ν i)) =
      ProjectionCycle.xVertex γ (fun i ↦ L (η i)) (fun i ↦ L (ν i)) := by
  -- Move the linear map through the vertex sum and use residual naturality.
  ext i
  rw [ProjectionCycle.xVertex_apply, ProjectionCycle.xVertex_apply, LinearMap.map_add,
    congrFun (mapResidualFamily L γ ν) i]

/-- A linear map carries a first-normal family to that of the mapped data. -/
private lemma mapFirstNormalFamily {N : ℕ} {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (γ : ℝ) (η ν : ZMod N → E) :
    (fun i ↦ L (ProjectionCycle.firstNormal γ η ν i)) =
      ProjectionCycle.firstNormal γ (fun i ↦ L (η i)) (fun i ↦ L (ν i)) := by
  -- Move the map through both differences and use first-vertex naturality.
  ext i
  rw [ProjectionCycle.firstNormal_apply, ProjectionCycle.firstNormal_apply,
    LinearMap.map_sub, LinearMap.map_sub, congrFun (mapXVertexFamily L γ η ν) i]

/-- A linear map carries a second-normal family to that of the mapped data. -/
private lemma mapSecondNormalFamily {N : ℕ} {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (γ : ℝ) (ν : ZMod N → E) :
    (fun i ↦ L (ProjectionCycle.secondNormal γ ν i)) =
      ProjectionCycle.secondNormal γ (fun i ↦ L (ν i)) := by
  -- Move the map through the normal sum and use residual naturality.
  ext i
  rw [ProjectionCycle.secondNormal_apply, ProjectionCycle.secondNormal_apply,
    LinearMap.map_add, congrFun (mapResidualFamily L γ ν) i]

/-- The standard first-block coefficient vector indexed by a cyclic phase. -/
def standardEta {N : ℕ} (i : ZMod N) : (Fin 2 × Fin N) → ℝ :=
  fun p ↦ if p.1 = 0 ∧ (p.2 : ZMod N) = i then 1 else 0

/-- Coordinate formula for a standard first-block coefficient vector. -/
theorem standardEta_apply {N : ℕ} (i : ZMod N) (p : Fin 2 × Fin N) :
    standardEta i p = if p.1 = 0 ∧ (p.2 : ZMod N) = i then 1 else 0 := by
  -- Evaluate the standard first-block coordinate vector.
  rfl

/-- The standard second-block coefficient vector indexed by a cyclic phase. -/
def standardNu {N : ℕ} (i : ZMod N) : (Fin 2 × Fin N) → ℝ :=
  fun p ↦ if p.1 = 1 ∧ (p.2 : ZMod N) = i then 1 else 0

/-- Coordinate formula for a standard second-block coefficient vector. -/
theorem standardNu_apply {N : ℕ} (i : ZMod N) (p : Fin 2 × Fin N) :
    standardNu i p = if p.1 = 1 ∧ (p.2 : ZMod N) = i then 1 else 0 := by
  -- Evaluate the standard second-block coordinate vector.
  rfl

/-- Gram-linear support against the origin and every distinct cyclic phase. -/
def Supports {N : ℕ}
    (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (p n : ZMod N → (Fin 2 × Fin N) → ℝ) : Prop :=
  ∀ i, 0 ≤ supportFunctional (n i) (p i) G ∧
    ∀ j, j ≠ i → 0 ≤ supportFunctional (n i) (p i - p j) G

/-- Gram support is the origin inequality together with every distinct-phase inequality. -/
theorem supports_iff {N : ℕ}
    {G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ}
    {p n : ZMod N → (Fin 2 × Fin N) → ℝ} :
    Supports G p n ↔
      ∀ i, 0 ≤ supportFunctional (n i) (p i) G ∧
        ∀ j, j ≠ i → 0 ≤ supportFunctional (n i) (p i - p j) G := by
  -- Expose the origin and distinct-phase inequalities in the support predicate.
  rfl

/-- A Gram support family is the geometric nonself-support family after canonical realization. -/
theorem supports_map_iff {N : ℕ}
    (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (hG : G.PosSemidef) (p n : ZMod N → (Fin 2 × Fin N) → ℝ) :
    Supports G p n ↔
      ProjectionCycle.NonselfSupports (fun i ↦ gramMap G (p i))
        (fun i ↦ gramMap G (n i)) := by
  -- Compare the two predicates pointwise using the square-root Gram identity.
  rw [supports_iff, ProjectionCycle.nonselfSupports_iff]
  constructor
  · intro hs i
    rcases hs i with ⟨horigin, hdistinct⟩
    constructor
    · rwa [gramMap_realInner G hG]
    · intro j hji
      rw [← (gramMap G).map_sub, gramMap_realInner G hG]
      exact hdistinct j hji
  · intro hs i
    rcases hs i with ⟨horigin, hdistinct⟩
    constructor
    · rwa [gramMap_realInner G hG] at horigin
    · intro j hji
      have hsupport := hdistinct j hji
      rw [← (gramMap G).map_sub, gramMap_realInner G hG] at hsupport
      exact hsupport

/-- The `(a,b)` phase block of a two-block Gram matrix. -/
def block {N : ℕ} (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (a b : Fin 2) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ G (a, i) (b, j)

/-- Entry formula for a block of a two-block Gram matrix. -/
theorem block_apply {N : ℕ} (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (a b : Fin 2) (i j : Fin N) :
    block G a b i j = G (a, i) (b, j) := by
  -- Evaluate the selected matrix block at its two phase indices.
  rfl

/-- Every two-block Gram entry depends only on the common cyclic phase difference. -/
def SimultaneouslyCyclic {N : ℕ}
    (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) : Prop :=
  ∀ (a b : Fin 2) (i j k l : Fin N), i - j = k - l →
    block G a b i j = block G a b k l

/-- Simultaneous cyclicity is common phase-difference invariance of every block. -/
theorem simultaneouslyCyclic_iff {N : ℕ}
    {G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ} :
    SimultaneouslyCyclic G ↔
      ∀ (a b : Fin 2) (i j k l : Fin N), i - j = k - l →
        block G a b i j = block G a b k l := by
  -- Expose the common phase-difference invariance condition.
  rfl

/-- Simultaneous cyclicity is equivalent to every Gram block having a circulant row. -/
theorem simultaneouslyCyclic_iff_circulantBlocks {N : ℕ}
    {G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ} :
    SimultaneouslyCyclic G ↔
      ∀ a b : Fin 2, ∃ r : Fin N → ℝ, block G a b = Matrix.circulant r := by
  -- Normalize each nonempty block by its column at phase zero.
  constructor
  · intro hcyclic a b
    cases N with
    | zero =>
        refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
        ext i
        exact Fin.elim0 i
    | succ n =>
        let r : Fin (n + 1) → ℝ := fun d ↦ block G a b d 0
        refine ⟨r, ?_⟩
        ext i j
        rw [Matrix.circulant_apply]
        simpa only [r] using hcyclic a b i j (i - j) 0 (sub_zero (i - j)).symm
  · intro hblocks a b i j k l hdifference
    rcases hblocks a b with ⟨r, hr⟩
    rw [hr, Matrix.circulant_apply, Matrix.circulant_apply, hdifference]

/-- Positive semidefiniteness, cyclic invariance, and both standard Gram support families. -/
structure Feasible {N : ℕ} (γ : ℝ)
    (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) : Prop where
  posSemidef : G.PosSemidef
  cyclic : SimultaneouslyCyclic G
  firstSupports :
    Supports G (ProjectionCycle.xVertex γ standardEta standardNu)
      (ProjectionCycle.firstNormal γ standardEta standardNu)
  secondSupports : Supports G standardEta (ProjectionCycle.secondNormal γ standardNu)

/-- Construct Gram feasibility from its semidefinite, cyclic, and support conditions. -/
def Feasible.ofConditions {N : ℕ} {γ : ℝ}
    {G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ}
    (posSemidef : G.PosSemidef) (cyclic : SimultaneouslyCyclic G)
    (firstSupports : Supports G (ProjectionCycle.xVertex γ standardEta standardNu)
      (ProjectionCycle.firstNormal γ standardEta standardNu))
    (secondSupports : Supports G standardEta (ProjectionCycle.secondNormal γ standardNu)) :
    Feasible γ G :=
  { posSemidef := posSemidef
    cyclic := cyclic
    firstSupports := firstSupports
    secondSupports := secondSupports }

/-- The defining semidefinite, cyclic, and two support conditions of Gram feasibility. -/
theorem feasible_iff {N : ℕ} (γ : ℝ)
    {G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ} :
    Feasible γ G ↔
      G.PosSemidef ∧ SimultaneouslyCyclic G ∧
        Supports G (ProjectionCycle.xVertex γ standardEta standardNu)
          (ProjectionCycle.firstNormal γ standardEta standardNu) ∧
        Supports G standardEta (ProjectionCycle.secondNormal γ standardNu) := by
  -- Split and reassemble the four fields of Gram feasibility.
  constructor
  · intro h
    exact ⟨h.posSemidef, h.cyclic, h.firstSupports, h.secondSupports⟩
  · rintro ⟨hG, hcyclic, hfirst, hsecond⟩
    exact Feasible.ofConditions hG hcyclic hfirst hsecond

/-- For fixed coefficient vectors, the Gram support functional is linear in the matrix. -/
theorem supportLinearInGram {N : ℕ} (z w : (Fin 2 × Fin N) → ℝ) (a b : ℝ)
    (G H : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) :
    supportFunctional z w (a • G + b • H) =
      a * supportFunctional z w G + b * supportFunctional z w H := by
  -- Apply additivity and homogeneity of the matrix-linear functional.
  simp only [map_add, map_smul, smul_eq_mul]

/-- Simultaneous cyclic invariance gives three circulant Gram blocks, with the fourth
mixed block determined by positive semidefinite symmetry. -/
theorem circulantBlocks {N : ℕ} (hN : 2 ≤ N)
    (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (hG : G.PosSemidef) (hcyclic : SimultaneouslyCyclic G) :
    ∃ r₀₀ r₀₁ r₁₁ : Fin N → ℝ,
      block G 0 0 = Matrix.circulant r₀₀ ∧
        block G 0 1 = Matrix.circulant r₀₁ ∧
          block G 1 1 = Matrix.circulant r₁₁ ∧
            block G 1 0 = (block G 0 1).transpose := by
  -- Extract the three independent circulant rows from simultaneous cyclicity.
  have hblocks := simultaneouslyCyclic_iff_circulantBlocks.mp hcyclic
  rcases hblocks 0 0 with ⟨r₀₀, hr₀₀⟩
  rcases hblocks 0 1 with ⟨r₀₁, hr₀₁⟩
  rcases hblocks 1 1 with ⟨r₁₁, hr₁₁⟩
  refine ⟨r₀₀, r₀₁, r₁₁, hr₀₀, hr₀₁, hr₁₁, ?_⟩
  -- Hermitian symmetry determines the remaining mixed block by transposition.
  ext i j
  rw [block_apply, Matrix.transpose_apply, block_apply]
  simpa only [star_trivial] using
    (hG.isHermitian.apply (1, i) (0, j)).symm

/-- Gram feasibility is equivalent to the projection-cycle conditions after square-root
realization under the positive-semidefinite and cyclic hypotheses. -/
theorem feasible_iff_projectionCycle {N : ℕ} (hN : 2 ≤ N) (γ : ℝ) (hγ : 0 < γ)
    (G : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (hG : G.PosSemidef) (hcyclic : SimultaneouslyCyclic G) :
    Feasible γ G ↔
      IsProjectionCycle γ (fun i ↦ gramMap G (standardEta i))
        (fun i ↦ gramMap G (standardNu i)) := by
  -- Remove the fixed semidefinite and cyclic fields, leaving the two support families.
  rw [feasible_iff, isProjectionCycle_iff]
  have hxVertex := mapXVertexFamily (gramMap G) γ standardEta standardNu
  have hfirstNormal := mapFirstNormalFamily (gramMap G) γ standardEta standardNu
  have hsecondNormal := mapSecondNormalFamily (gramMap G) γ standardNu
  constructor
  · rintro ⟨_, _, hfirst, hsecond⟩
    constructor
    · rw [supports_map_iff G hG] at hfirst
      simpa only [hxVertex, hfirstNormal] using hfirst
    · rw [supports_map_iff G hG] at hsecond
      simpa only [hsecondNormal] using hsecond
  · rintro ⟨hfirst, hsecond⟩
    refine ⟨hG, hcyclic, ?_, ?_⟩
    · rw [supports_map_iff G hG]
      simpa only [hxVertex, hfirstNormal] using hfirst
    · rw [supports_map_iff G hG]
      simpa only [hsecondNormal] using hsecond

end GramCycle

end

end ConsensusADMM
