/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Threshold
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.FixedPolytopes
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycleTrajectory
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycleStrictification
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Optimality
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.SupportedObjectives
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.SmoothCycle
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.GeometricGrowth
public import glowinski_admm_counterexample.ReasLib.Convex.ExtendedReal
public import glowinski_admm_counterexample.ReasLib.Convex.Polyhedral
public import glowinski_admm_counterexample.ReasLib.Convex.PiecewiseQuadratic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

namespace ConsensusADMM

open scoped MatrixOrder

/-- Every factor on the critical half-line is positive. -/
private lemma criticalFactorLE_imp_pos {γ : ℝ} (lowerBound : criticalFactor ≤ γ) :
    0 < γ := by
  -- Transitivity transfers positivity of the endpoint to the whole half-line.
  exact criticalFactor_pos.trans_le lowerBound

/-- The critical multiplier factor lies below the strictification endpoint `2`. -/
private lemma criticalFactor_lt_two : criticalFactor < 2 := by
  -- The explicit rational formula makes the strict bound a numerical check.
  rw [criticalFactor_eq]
  norm_num

/-- An injective family indexed by `Fin 48`, read cyclically along `ℕ`, has
minimal positive period `48`. -/
private lemma fin48Sequence_exactPeriod {α : Type u} (phase : Fin 48 → α)
    (phase_injective : Function.Injective phase) :
    Function.Periodic (fun k : ℕ ↦ phase (Fin.ofNat 48 k)) 48 ∧
      ∀ n, 0 < n →
        Function.Periodic (fun k : ℕ ↦ phase (Fin.ofNat 48 k)) n → 48 ≤ n := by
  -- Adding 48 does not change the residue class indexing the phase family.
  constructor
  · intro k
    apply congrArg phase
    ext
    simp [Fin.ofNat]
  -- Any other positive period identifies phase `n` with phase zero; injectivity
  -- therefore forces divisibility by 48 and hence the desired lower bound.
  · intro n n_pos periodic
    have phase_eq : Fin.ofNat 48 n = Fin.ofNat 48 0 := by
      apply phase_injective
      simpa using periodic 0
    have mod_eq_zero : n % 48 = 0 := by
      have value_eq := congrArg Fin.val phase_eq
      simpa [Fin.ofNat] using value_eq
    have divides : 48 ∣ n := Nat.dvd_of_mod_eq_zero mod_eq_zero
    exact Nat.le_of_dvd n_pos divides

/-- A post-update ADMM state identified with an injective cyclic family of 48
phases has exact period `48`. -/
private lemma hasExactPeriod_of_fin48State {E : Type u}
    (x y dual : ℕ → E) (phase : Fin 48 → E × E × E)
    (phase_injective : Function.Injective phase)
    (state_eq : ∀ k, (x (k + 1), y (k + 1), dual (k + 1)) = phase (Fin.ofNat 48 k)) :
    HasExactPeriod 48 x y dual := by
  -- Transfer periodicity and its minimality from the injective finite family to
  -- the displayed post-update state without unfolding any cycle construction.
  rw [exactPeriod_iff]
  obtain ⟨phase_periodic, phase_minimal⟩ :=
    fin48Sequence_exactPeriod phase phase_injective
  constructor
  · intro k
    simp only
    rw [state_eq (k + 48), state_eq k]
    exact phase_periodic k
  · intro n n_pos state_periodic
    apply phase_minimal n n_pos
    intro k
    simp only
    rw [← state_eq (k + n), ← state_eq k]
    exact state_periodic k

/-- Indicators of two sets containing the origin have the origin as a KKT point
and a primal minimizer, with objective value zero. -/
private lemma indicatorOriginOptimality {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X Y : Set E} (zero_mem_X : 0 ∈ X) (zero_mem_Y : 0 ∈ Y) :
    IsKKT (extendedIndicator X) (extendedIndicator Y) 0 0 0 ∧
      IsPrimalMinimizer (extendedIndicator X) (extendedIndicator Y) 0 ∧
      extendedIndicator X 0 + extendedIndicator Y 0 = 0 := by
  -- At the zero multiplier, both KKT inequalities reduce to nonnegativity of
  -- an indicator; membership of the origin selects its finite branch.
  have kkt : IsKKT (extendedIndicator X) (extendedIndicator Y) 0 0 0 := by
    rw [kkt_iff]
    refine ⟨rfl, ?_, ?_⟩
    · intro z
      by_cases z_mem : z ∈ X
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem z_mem]
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_not_mem z_mem]
    · intro z
      by_cases z_mem : z ∈ Y
      · simp [extendedIndicator_of_mem zero_mem_Y, extendedIndicator_of_mem z_mem]
      · simp [extendedIndicator_of_mem zero_mem_Y, extendedIndicator_of_not_mem z_mem]
  -- The same two-branch calculation shows that no feasible or infeasible
  -- comparison point has objective below the origin.
  have primal : IsPrimalMinimizer (extendedIndicator X) (extendedIndicator Y) 0 := by
    rw [primalMinimizer_iff]
    intro z
    by_cases z_mem_X : z ∈ X
    · by_cases z_mem_Y : z ∈ Y
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem zero_mem_Y,
          extendedIndicator_of_mem z_mem_X, extendedIndicator_of_mem z_mem_Y]
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem zero_mem_Y,
          extendedIndicator_of_mem z_mem_X, extendedIndicator_of_not_mem z_mem_Y]
    · by_cases z_mem_Y : z ∈ Y
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem zero_mem_Y,
          extendedIndicator_of_not_mem z_mem_X, extendedIndicator_of_mem z_mem_Y]
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem zero_mem_Y,
          extendedIndicator_of_not_mem z_mem_X, extendedIndicator_of_not_mem z_mem_Y]
  -- Both indicators vanish at the origin, completing the three conclusions.
  have value : extendedIndicator X 0 + extendedIndicator Y 0 = 0 := by
    rw [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem zero_mem_Y]
    exact add_zero 0
  exact ⟨kkt, primal, value⟩

/-- The convex hull of finitely many points in the ambient Euclidean space is
a compact convex polytope. -/
private lemma finsetConvexHull_isCompactConvexPolytope
    (vertices : Finset (EuclideanSpace ℝ (Fin 96))) :
    IsCompactConvexPolytope (convexHull ℝ (vertices : Set (EuclideanSpace ℝ (Fin 96)))) := by
  -- Finite sets are compact, and convex hulls of compact sets remain compact
  -- in this finite-dimensional real space.
  rw [compactConvexPolytope_iff]
  refine ⟨?_, convex_convexHull ℝ _, vertices, rfl⟩
  exact (Set.toFinite (vertices : Set (EuclideanSpace ℝ (Fin 96)))).isCompact_convexHull ℝ

/-- A real linear isometric equivalence carries compact convex polytopes to compact
convex polytopes. -/
private lemma isCompactConvexPolytope_image_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {X : Set E} (hX : IsCompactConvexPolytope X) :
    IsCompactConvexPolytope (e '' X) := by
  classical
  -- Transport compactness and convexity, then map one finite vertex presentation.
  rw [compactConvexPolytope_iff] at hX ⊢
  obtain ⟨compact_X, convex_X, vertices, vertices_eq⟩ := hX
  refine ⟨compact_X.image e.continuous, convex_X.is_linear_image e.toLinearMap.isLinear,
    vertices.image e, ?_⟩
  rw [Finset.coe_image, vertices_eq]
  exact e.toLinearMap.image_convexHull _

/-- A linear isometry commutes with the residual family of cyclic multiplier data. -/
private lemma projectionCycleResidual_comp_linearIsometry
    {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (gamma : ℝ) (nu : ZMod N → E) (i : ZMod N) :
    ProjectionCycle.residual gamma (fun j ↦ e (nu j)) i =
      e (ProjectionCycle.residual gamma nu i) := by
  -- Move the isometry through the defining scalar multiple and difference.
  simp only [ProjectionCycle.residual_apply, LinearIsometry.map_smul,
    LinearIsometry.map_sub]

/-- A linear isometry commutes with the first vertex family of projection-cycle data. -/
private lemma projectionCycleXVertex_comp_linearIsometry
    {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (gamma : ℝ) (eta nu : ZMod N → E) (i : ZMod N) :
    ProjectionCycle.xVertex gamma (fun j ↦ e (eta j)) (fun j ↦ e (nu j)) i =
      e (ProjectionCycle.xVertex gamma eta nu i) := by
  -- Transport the vertex sum after transporting its residual term.
  rw [ProjectionCycle.xVertex_apply, ProjectionCycle.xVertex_apply,
    projectionCycleResidual_comp_linearIsometry, LinearIsometry.map_add]

/-- A linear isometry commutes with the first supporting-normal family. -/
private lemma projectionCycleFirstNormal_comp_linearIsometry
    {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (gamma : ℝ) (eta nu : ZMod N → E) (i : ZMod N) :
    ProjectionCycle.firstNormal gamma (fun j ↦ e (eta j)) (fun j ↦ e (nu j)) i =
      e (ProjectionCycle.firstNormal gamma eta nu i) := by
  -- Transport both differences after normalizing the mapped vertex.
  rw [ProjectionCycle.firstNormal_apply, ProjectionCycle.firstNormal_apply,
    projectionCycleXVertex_comp_linearIsometry, LinearIsometry.map_sub,
    LinearIsometry.map_sub]

/-- A linear isometry commutes with the second supporting-normal family. -/
private lemma projectionCycleSecondNormal_comp_linearIsometry
    {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (gamma : ℝ) (nu : ZMod N → E) (i : ZMod N) :
    ProjectionCycle.secondNormal gamma (fun j ↦ e (nu j)) i =
      e (ProjectionCycle.secondNormal gamma nu i) := by
  -- Transport the normal sum after normalizing the mapped residual.
  rw [ProjectionCycle.secondNormal_apply, ProjectionCycle.secondNormal_apply,
    projectionCycleResidual_comp_linearIsometry, LinearIsometry.map_add]

/-- The coordinate inclusion from `Fin d` to `Fin n` sends each standard
Euclidean basis vector to the corresponding standard basis vector. -/
private noncomputable def euclideanFinInclusionLinearMap {d n : ℕ} (hdn : d ≤ n) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.constr ℝ
    (fun i ↦ EuclideanSpace.basisFun (Fin n) ℝ (Fin.castLE hdn i))

/-- The coordinate-inclusion linear map sends standard basis vectors to their
images under `Fin.castLE`. -/
private lemma euclideanFinInclusionLinearMap_basis {d n : ℕ} (hdn : d ≤ n)
    (i : Fin d) :
    euclideanFinInclusionLinearMap hdn (EuclideanSpace.basisFun (Fin d) ℝ i) =
      EuclideanSpace.basisFun (Fin n) ℝ (Fin.castLE hdn i) := by
  -- The map was constructed by prescribing precisely these basis values.
  exact (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.constr_basis ℝ _ i

/-- The images of the standard basis under coordinate inclusion form an
orthonormal family. -/
private lemma euclideanFinInclusionLinearMap_orthonormal {d n : ℕ} (hdn : d ≤ n) :
    Orthonormal ℝ
      (euclideanFinInclusionLinearMap hdn ∘ EuclideanSpace.basisFun (Fin d) ℝ) := by
  -- Identify the image family with a subfamily of the ambient standard basis.
  have image_eq :
      euclideanFinInclusionLinearMap hdn ∘ EuclideanSpace.basisFun (Fin d) ℝ =
        EuclideanSpace.basisFun (Fin n) ℝ ∘ Fin.castLE hdn := by
    funext i
    exact euclideanFinInclusionLinearMap_basis hdn i
  rw [image_eq]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.comp _
    (Fin.castLE_injective hdn)

/-- Zero-padding the final coordinates gives a linear isometric embedding
`EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin n)` whenever `d ≤ n`. -/
private noncomputable def euclideanFinInclusion {d n : ℕ} (hdn : d ≤ n) :
    EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (euclideanFinInclusionLinearMap hdn).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal
    (euclideanFinInclusionLinearMap_orthonormal hdn)

/-- The coordinate isometry agrees with its prescribed underlying linear map. -/
private lemma euclideanFinInclusion_apply {d n : ℕ} (hdn : d ≤ n)
    (x : EuclideanSpace ℝ (Fin d)) :
    euclideanFinInclusion hdn x = euclideanFinInclusionLinearMap hdn x := by
  -- `isometryOfOrthonormal` changes only the bundled norm-preservation field.
  rfl

/-- Linear isometries preserve projection cycles. -/
private lemma isProjectionCycle_comp_linearIsometry
    {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (gamma : ℝ) (eta nu : ZMod N → E)
    (cycle : IsProjectionCycle gamma eta nu) :
    IsProjectionCycle gamma (fun i ↦ e (eta i)) (fun i ↦ e (nu i)) := by
  -- Rewrite every mapped support pairing to its source pairing.
  constructor
  · intro i
    refine ⟨?_, ?_⟩
    · rw [projectionCycleFirstNormal_comp_linearIsometry,
        projectionCycleXVertex_comp_linearIsometry, LinearIsometry.inner_map_map]
      exact (cycle.1 i).1
    · intro j hj
      rw [projectionCycleFirstNormal_comp_linearIsometry,
        projectionCycleXVertex_comp_linearIsometry,
        projectionCycleXVertex_comp_linearIsometry, ← LinearIsometry.map_sub,
        LinearIsometry.inner_map_map]
      exact (cycle.1 i).2 j hj
  · intro i
    refine ⟨?_, ?_⟩
    · rw [projectionCycleSecondNormal_comp_linearIsometry,
        LinearIsometry.inner_map_map]
      exact (cycle.2 i).1
    · intro j hj
      rw [projectionCycleSecondNormal_comp_linearIsometry, ← LinearIsometry.map_sub,
        LinearIsometry.inner_map_map]
      exact (cycle.2 i).2 j hj

/-- Linear isometries preserve strict projection cycles. -/
private lemma isStrictProjectionCycle_comp_linearIsometry
    {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (gamma : ℝ) (eta nu : ZMod N → E)
    (cycle : IsStrictProjectionCycle gamma eta nu) :
    IsStrictProjectionCycle gamma (fun i ↦ e (eta i)) (fun i ↦ e (nu i)) := by
  -- Strictness is expressed only through inner products of vertices, normals,
  -- and their differences, all of which are preserved by a linear isometry.
  constructor
  · intro i
    refine ⟨?_, ?_⟩
    · rw [projectionCycleFirstNormal_comp_linearIsometry,
        projectionCycleXVertex_comp_linearIsometry, LinearIsometry.inner_map_map]
      exact (cycle.1 i).1
    · intro j hj
      rw [projectionCycleFirstNormal_comp_linearIsometry,
        projectionCycleXVertex_comp_linearIsometry,
        projectionCycleXVertex_comp_linearIsometry, ← LinearIsometry.map_sub,
        LinearIsometry.inner_map_map]
      exact (cycle.1 i).2 j hj
  · intro i
    refine ⟨?_, ?_⟩
    · rw [projectionCycleSecondNormal_comp_linearIsometry,
        LinearIsometry.inner_map_map]
      exact (cycle.2 i).1
    · intro j hj
      rw [projectionCycleSecondNormal_comp_linearIsometry, ← LinearIsometry.map_sub,
        LinearIsometry.inner_map_map]
      exact (cycle.2 i).2 j hj

/-- A linear isometry sends the first projection-cycle hull to the hull of the
transported cycle. -/
private lemma projectionCycleXSet_comp_linearIsometry
    {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (gamma : ℝ) (eta nu : ZMod N → E) :
    ProjectionCycle.xSet gamma (fun i ↦ e (eta i)) (fun i ↦ e (nu i)) =
      e '' ProjectionCycle.xSet gamma eta nu := by
  -- Move the convex hull through the linear map and identify its generators.
  rw [ProjectionCycle.xSet_def, ProjectionCycle.xSet_def]
  rw [show (e : E → F) = e.toLinearMap from rfl, e.toLinearMap.image_convexHull]
  congr 1
  ext z
  constructor
  · intro hz
    rcases hz with hz | hz
    · refine ⟨0, Set.mem_insert 0 _, ?_⟩
      simpa only [hz, map_zero]
    · obtain ⟨i, rfl⟩ := hz
      refine ⟨ProjectionCycle.xVertex gamma eta nu i, ?_, ?_⟩
      · exact Set.mem_insert_of_mem 0 ⟨i, rfl⟩
      · exact (projectionCycleXVertex_comp_linearIsometry e gamma eta nu i).symm
  · rintro ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · left
      simpa only [hz, map_zero]
    · obtain ⟨i, rfl⟩ := hz
      right
      exact ⟨i, projectionCycleXVertex_comp_linearIsometry e gamma eta nu i⟩

/-- A linear isometry sends the second projection-cycle hull to the hull of the
transported cycle. -/
private lemma projectionCycleYSet_comp_linearIsometry
    {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (eta : ZMod N → E) :
    ProjectionCycle.ySet (fun i ↦ e (eta i)) = e '' ProjectionCycle.ySet eta := by
  -- Move the convex hull through the linear map and identify its generators.
  rw [ProjectionCycle.ySet_def, ProjectionCycle.ySet_def]
  rw [show (e : E → F) = e.toLinearMap from rfl, e.toLinearMap.image_convexHull]
  congr 1
  ext z
  constructor
  · intro hz
    rcases hz with hz | hz
    · refine ⟨0, Set.mem_insert 0 _, ?_⟩
      simpa only [hz, map_zero]
    · obtain ⟨i, rfl⟩ := hz
      exact ⟨eta i, Set.mem_insert_of_mem 0 ⟨i, rfl⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · left
      simpa only [hz, map_zero]
    · obtain ⟨i, rfl⟩ := hz
      right
      exact ⟨i, rfl⟩

/-- The rational period-48 Gram data realize two fixed origin-containing
compact convex polytopes and a supported cyclic configuration on the whole
critical half-line. -/
private theorem period48GramSupportCertificate :
    ∃ X Y : Set (EuclideanSpace ℝ (Fin 96)),
      IsCompactConvexPolytope X ∧ IsCompactConvexPolytope Y ∧
      0 ∈ X ∧ 0 ∈ Y ∧
      ∀ γ, criticalFactor ≤ γ →
        ∃ eta nu : ZMod 48 → EuclideanSpace ℝ (Fin 96),
          ∃ c_r : ℝ,
          ∃ phase : Fin 48 →
              EuclideanSpace ℝ (Fin 96) × EuclideanSpace ℝ (Fin 96) ×
                EuclideanSpace ℝ (Fin 96),
            0 < c_r ∧
            IsProjectionCycle γ eta nu ∧
            ProjectionCycle.xSet γ eta nu = X ∧
            ProjectionCycle.ySet eta = Y ∧
            Function.Injective phase ∧
            (∀ k,
              (ProjectionCycle.xSequence γ eta nu (k + 1),
                  ProjectionCycle.ySequence eta (k + 1),
                  ProjectionCycle.dualSequence nu (k + 1)) =
                phase (Fin.ofNat 48 k)) ∧
            ∀ k,
              ‖ProjectionCycle.xSequence γ eta nu (k + 1) -
                  ProjectionCycle.ySequence eta (k + 1)‖ = c_r := by
  classical
  -- Factor the positive-definite Gram matrix and reindex its Euclidean realization
  -- from block coordinates to the required 96 flat coordinates.
  obtain ⟨S, factor_source⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := Period48.gramMatrix)).mp
    Period48.FixedPolytopes.gramMatrix_posDef.posSemidef.nonneg
  have factor : S.transpose * S = Period48.gramMatrix := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using factor_source.symm
  let e : EuclideanSpace ℝ (Fin 2 × Fin 48) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 96) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finProdFinEquiv
  let X := e '' Period48.Realization.xSet S
  let Y := e '' Period48.Realization.ySet S
  have compact_sets := Period48.FixedPolytopes.xSet_ySet_isCompactConvexPolytope S
  have compact_X : IsCompactConvexPolytope X := by
    exact isCompactConvexPolytope_image_linearIsometryEquiv e compact_sets.1
  have compact_Y : IsCompactConvexPolytope Y := by
    exact isCompactConvexPolytope_image_linearIsometryEquiv e compact_sets.2
  have zero_mem_X : 0 ∈ X := by
    refine ⟨0, ?_, ?_⟩
    · rw [Period48.Realization.xSet_def]
      exact subset_convexHull ℝ _ (Set.mem_insert 0 _)
    · exact e.map_zero
  have zero_mem_Y : 0 ∈ Y := by
    refine ⟨0, ?_, ?_⟩
    · rw [Period48.Realization.ySet_def]
      exact subset_convexHull ℝ _ (Set.mem_insert 0 _)
    · exact e.map_zero
  refine ⟨X, Y, compact_X, compact_Y, zero_mem_X, zero_mem_Y, ?_⟩
  intro gamma lowerBound
  let eta : ZMod 48 → EuclideanSpace ℝ (Fin 96) :=
    fun i ↦ e (Period48.Realization.eta S i)
  let nu : ZMod 48 → EuclideanSpace ℝ (Fin 96) :=
    fun i ↦ e (Period48.Realization.nu S gamma i)
  let phase : Fin 48 →
      EuclideanSpace ℝ (Fin 96) × EuclideanSpace ℝ (Fin 96) ×
        EuclideanSpace ℝ (Fin 96) := fun i ↦
    (e (ProjectionCycle.xVertex gamma (Period48.Realization.eta S)
        (Period48.Realization.nu S gamma) (ZMod.finEquiv 48 i)),
      e (Period48.Realization.eta S (ZMod.finEquiv 48 i)),
      e (Period48.Realization.nu S gamma (ZMod.finEquiv 48 i)))
  have cycle_source := Period48.FixedPolytopes.isProjectionCycle S factor gamma lowerBound
  have cycle : IsProjectionCycle gamma eta nu := by
    exact isProjectionCycle_comp_linearIsometry e.toLinearIsometry gamma _ _ cycle_source
  obtain ⟨c_r, residual_pos, residual_eq⟩ :=
    Period48.FixedPolytopes.constantPositiveResidual S factor gamma lowerBound
  have sets_source := Period48.FixedPolytopes.xSet_ySet_eq S gamma lowerBound
  have phase_injective : Function.Injective phase := by
    intro i j phase_eq
    apply (ZMod.finEquiv 48).injective
    apply Period48.FixedPolytopes.statePhase_injective S factor gamma
    have x_eq := e.injective (congrArg (fun state ↦ state.1) phase_eq)
    have y_eq := e.injective (congrArg (fun state ↦ state.2.1) phase_eq)
    have dual_eq := e.injective (congrArg (fun state ↦ state.2.2) phase_eq)
    exact Prod.ext x_eq (Prod.ext y_eq dual_eq)
  refine ⟨eta, nu, c_r, phase, residual_pos, cycle, ?_, ?_, phase_injective, ?_, ?_⟩
  · -- The first mapped hull is the fixed image `X`, independently of `gamma`.
    calc
      ProjectionCycle.xSet gamma eta nu =
          e '' ProjectionCycle.xSet gamma (Period48.Realization.eta S)
            (Period48.Realization.nu S gamma) := by
              exact projectionCycleXSet_comp_linearIsometry e.toLinearIsometry gamma _ _
      _ = e '' Period48.Realization.xSet S := congrArg (fun Z ↦ e '' Z) sets_source.1
      _ = X := rfl
  · -- The second mapped hull is the fixed image `Y`.
    calc
      ProjectionCycle.ySet eta = e '' ProjectionCycle.ySet (Period48.Realization.eta S) := by
        exact projectionCycleYSet_comp_linearIsometry e.toLinearIsometry _
      _ = e '' Period48.Realization.ySet S := congrArg (fun Z ↦ e '' Z) sets_source.2
      _ = Y := rfl
  · -- Each post-update state is the transported state at the corresponding phase.
    intro k
    simp only [ProjectionCycle.xSequence_succ, ProjectionCycle.ySequence_succ,
      ProjectionCycle.dualSequence_succ, eta, nu, phase,
      projectionCycleXVertex_comp_linearIsometry]
    rfl
  · -- Isometry preserves the common positive residual norm.
    intro k
    simp only [ProjectionCycle.xSequence_succ, ProjectionCycle.ySequence_succ,
      ProjectionCycle.xVertex_apply, eta, nu, add_sub_cancel_left]
    change ‖ProjectionCycle.residual gamma
      (fun i ↦ e.toLinearIsometry (Period48.Realization.nu S gamma i)) (k : ZMod 48)‖ = c_r
    rw [projectionCycleResidual_comp_linearIsometry, LinearIsometry.norm_map]
    exact residual_eq (k : ZMod 48)

/-- One fixed pair of compact convex polytopes in `ℝ⁹⁶` supports, for every
multiplier factor at least `criticalFactor`, a unique-update consensus ADMM
trajectory of exact period `48` and constant positive residual. -/
theorem fixedPolytopes :
    ∃ X Y : Set (EuclideanSpace ℝ (Fin 96)),
      IsCompactConvexPolytope X ∧ IsCompactConvexPolytope Y ∧
      IsKKT (extendedIndicator X) (extendedIndicator Y) 0 0 0 ∧
      IsPrimalMinimizer (extendedIndicator X) (extendedIndicator Y) 0 ∧
      extendedIndicator X 0 + extendedIndicator Y 0 = 0 ∧
      ∀ γ, criticalFactor ≤ γ →
        ∃ x y dual : ℕ → EuclideanSpace ℝ (Fin 96), ∃ c_r : ℝ,
          0 < c_r ∧
          IsTrajectory γ (extendedIndicator X) (extendedIndicator Y) x y dual ∧
          HasUniqueUpdates (extendedIndicator X) (extendedIndicator Y) x y dual ∧
          HasExactPeriod 48 x y dual ∧
          ∀ k, ‖x (k + 1) - y (k + 1)‖ = c_r := by
  -- Unpack only the stable geometric interface; the generic projection-cycle
  -- API supplies both optimization updates from its support inequalities.
  obtain ⟨X, Y, compact_X, compact_Y, zero_mem_X, zero_mem_Y, cycles⟩ :=
    period48GramSupportCertificate
  -- Generic indicator optimality supplies the static clauses independently
  -- of the numerical period-48 construction.
  obtain ⟨kkt, primal, value⟩ := indicatorOriginOptimality zero_mem_X zero_mem_Y
  refine ⟨X, Y, compact_X, compact_Y, kkt, primal, value, ?_⟩
  intro γ lowerBound
  obtain ⟨eta, nu, c_r, phase, residual_pos, cycle, xSet_eq, ySet_eq,
    phase_injective, state_eq, residual_eq⟩ := cycles γ lowerBound
  have gamma_pos : 0 < γ := criticalFactorLE_imp_pos lowerBound
  have two_le_phases : 2 ≤ 48 := by
    norm_num
  have trajectory :=
    IsProjectionCycle.isTrajectory γ eta nu two_le_phases gamma_pos cycle
  have unique_updates :=
    IsProjectionCycle.hasUniqueUpdates γ eta nu two_le_phases gamma_pos cycle
  -- Rewrite the generic cycle hulls to the fixed polytopes, then transfer
  -- exactness from the injective phase family.
  refine ⟨ProjectionCycle.xSequence γ eta nu, ProjectionCycle.ySequence eta,
    ProjectionCycle.dualSequence nu, c_r, residual_pos, ?_, ?_, ?_, residual_eq⟩
  · simpa only [xSet_eq, ySet_eq] using trajectory
  · simpa only [xSet_eq, ySet_eq] using unique_updates
  · exact hasExactPeriod_of_fin48State _ _ _ phase phase_injective state_eq

/-! The following adapter records exactly the hypotheses needed by the generic
strictification theorem.  Keeping this finite certificate separate avoids
repeating the Gram-factor and support rewrites in each later construction. -/

/-- A square Gram factor of the positive-definite period-48 matrix acts
injectively on its Euclidean coefficient space. -/
private lemma gramFactorEuclidean_injective
    (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
    (factor : S.transpose * S = Period48.gramMatrix) :
    Function.Injective (Matrix.toEuclideanLin S) := by
  -- A nonzero coefficient difference has positive Gram quadratic form, whereas
  -- equality of its two images would force that quadratic form to vanish.
  intro u v huv
  have image_zero : Matrix.toEuclideanLin S (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have quadratic_zero : Period48.FixedPolytopes.coefficientQuadratic
      (WithLp.ofLp (u - v)) = 0 := by
    calc
      Period48.FixedPolytopes.coefficientQuadratic (WithLp.ofLp (u - v)) =
          ‖WithLp.toLp 2 (S.mulVec (WithLp.ofLp (u - v)))‖ ^ 2 :=
        (Period48.FixedPolytopes.norm_sq_toLp_mulVec S factor _).symm
      _ = ‖Matrix.toEuclideanLin S (u - v)‖ ^ 2 := by
        rw [Matrix.toLpLin_apply]
      _ = 0 := by rw [image_zero, norm_zero]; norm_num
  have coefficient_zero : WithLp.ofLp (u - v) = 0 := by
    by_contra coefficient_ne
    have quadratic_pos :=
      Period48.FixedPolytopes.coefficientQuadratic_pos coefficient_ne
    linarith
  exact sub_eq_zero.mp (WithLp.ofLp_injective 2 coefficient_zero)

/-- The Gram factor is a linear equivalence of its square Euclidean coefficient
space. -/
private noncomputable def gramFactorLinearEquiv
    (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
    (factor : S.transpose * S = Period48.gramMatrix) :
    EuclideanSpace ℝ (Fin 2 × Fin 48) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin 2 × Fin 48) :=
  LinearEquiv.ofInjectiveEndo (Matrix.toEuclideanLin S)
    (gramFactorEuclidean_injective S factor)

/-- The linear equivalence induced by a Gram factor acts by matrix-vector
multiplication. -/
private lemma gramFactorLinearEquiv_apply
    (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
    (factor : S.transpose * S = Period48.gramMatrix)
    (u : EuclideanSpace ℝ (Fin 2 × Fin 48)) :
    gramFactorLinearEquiv S factor u = Matrix.toEuclideanLin S u := by
  -- The finite-dimensional upgrade retains the original linear map.
  rfl

/-- The coefficient-space isometry induced by one forward cyclic phase shift. -/
private noncomputable def coefficientPhaseShift :
    EuclideanSpace ℝ (Fin 2 × Fin 48) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 2 × Fin 48) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Period48.Coefficient.phaseShift (-1)).symm

/-- The forward coefficient phase shift advances the first-block basis family. -/
private lemma coefficientPhaseShift_eta (i : ZMod 48) :
    coefficientPhaseShift (WithLp.toLp 2 (Period48.Coefficient.eta i)) =
      WithLp.toLp 2 (Period48.Coefficient.eta (i + 1)) := by
  -- Precomposition by the inverse coordinate permutation advances the phase.
  apply WithLp.ofLp_injective
  funext p
  simp only [coefficientPhaseShift, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, Equiv.symm_symm, WithLp.ofLp_toLp]
  rw [Period48.Coefficient.eta_phaseShift]
  congr 1
  abel

/-- The forward coefficient phase shift advances the second-block basis family. -/
private lemma coefficientPhaseShift_nu (i : ZMod 48) :
    coefficientPhaseShift (WithLp.toLp 2 (Period48.Coefficient.nu i)) =
      WithLp.toLp 2 (Period48.Coefficient.nu (i + 1)) := by
  -- The same coordinate permutation advances the multiplier coefficient phase.
  apply WithLp.ofLp_injective
  funext p
  simp only [coefficientPhaseShift, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, Equiv.symm_symm, WithLp.ofLp_toLp]
  rw [Period48.Coefficient.nu_phaseShift]
  congr 1
  abel

/-- The forward coefficient phase shift preserves the period-48 Gram quadratic
form. -/
private lemma coefficientQuadratic_phaseShift
    (u : EuclideanSpace ℝ (Fin 2 × Fin 48)) :
    Period48.FixedPolytopes.coefficientQuadratic
        (WithLp.ofLp (coefficientPhaseShift u)) =
      Period48.FixedPolytopes.coefficientQuadratic (WithLp.ofLp u) := by
  -- Normalize the reindexed coefficient function and apply Gram invariance.
  have shifted : WithLp.ofLp (coefficientPhaseShift u) =
      fun p ↦ WithLp.ofLp u (Period48.Coefficient.phaseShift (-1) p) := by
    funext p
    rfl
  rw [shifted]
  exact Period48.FixedPolytopes.coefficientQuadratic_comp_phaseShift (-1) _

/-- Conjugating the coefficient phase shift through a Gram factor preserves
the ambient Euclidean norm. -/
private lemma gramConjugatedPhaseShift_norm
    (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
    (factor : S.transpose * S = Period48.gramMatrix)
    (x : EuclideanSpace ℝ (Fin 2 × Fin 48)) :
    ‖gramFactorLinearEquiv S factor
        (coefficientPhaseShift ((gramFactorLinearEquiv S factor).symm x))‖ = ‖x‖ := by
  -- Compare squared norms through the common Gram quadratic form, then use
  -- nonnegativity of norms to remove the squares.
  let u := (gramFactorLinearEquiv S factor).symm x
  have source_eq : gramFactorLinearEquiv S factor u = x := by
    exact (gramFactorLinearEquiv S factor).apply_symm_apply x
  have square_eq :
      ‖gramFactorLinearEquiv S factor (coefficientPhaseShift u)‖ ^ 2 =
        ‖gramFactorLinearEquiv S factor u‖ ^ 2 := by
    calc
      ‖gramFactorLinearEquiv S factor (coefficientPhaseShift u)‖ ^ 2 =
          Period48.FixedPolytopes.coefficientQuadratic
            (WithLp.ofLp (coefficientPhaseShift u)) := by
        rw [gramFactorLinearEquiv_apply, Matrix.toLpLin_apply,
          Period48.FixedPolytopes.norm_sq_toLp_mulVec S factor]
      _ = Period48.FixedPolytopes.coefficientQuadratic (WithLp.ofLp u) :=
        coefficientQuadratic_phaseShift u
      _ = ‖gramFactorLinearEquiv S factor u‖ ^ 2 := by
        rw [gramFactorLinearEquiv_apply, Matrix.toLpLin_apply,
          Period48.FixedPolytopes.norm_sq_toLp_mulVec S factor]
  rw [source_eq] at square_eq
  change ‖gramFactorLinearEquiv S factor (coefficientPhaseShift u)‖ = ‖x‖
  nlinarith [norm_nonneg
    (gramFactorLinearEquiv S factor (coefficientPhaseShift u)), norm_nonneg x]

/-- The orthogonal phase map obtained by conjugating coefficient rotation
through a Gram factor. -/
private noncomputable def gramPhaseShiftIsometry
    (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
    (factor : S.transpose * S = Period48.gramMatrix) :
    EuclideanSpace ℝ (Fin 2 × Fin 48) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 2 × Fin 48) :=
  { toLinearEquiv := (gramFactorLinearEquiv S factor).symm.trans
      (coefficientPhaseShift.toLinearEquiv.trans (gramFactorLinearEquiv S factor))
    norm_map' := gramConjugatedPhaseShift_norm S factor }

/-- The realized critical cycle has an orthogonal symmetry advancing both
phase families. -/
private lemma criticalCycle_hasOrthogonalCyclicSymmetry
    (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
    (factor : S.transpose * S = Period48.gramMatrix) :
    ProjectionCycle.HasOrthogonalCyclicSymmetry
      (Period48.Realization.eta S)
      (Period48.Realization.nu S criticalFactor) := by
  -- The conjugated coefficient shift advances the realized `eta` and `nu`
  -- families, while its norm law supplies orthogonality.
  refine ⟨gramPhaseShiftIsometry S factor, ?_⟩
  intro i
  constructor
  · change gramFactorLinearEquiv S factor
        (coefficientPhaseShift ((gramFactorLinearEquiv S factor).symm
          (gramFactorLinearEquiv S factor (WithLp.toLp 2 (Period48.Coefficient.eta i))))) =
      gramFactorLinearEquiv S factor (WithLp.toLp 2 (Period48.Coefficient.eta (i + 1)))
    rw [LinearEquiv.symm_apply_apply, coefficientPhaseShift_eta]
  · rw [Period48.Realization.nu_apply, Period48.Realization.nu_apply,
      Period48.Realization.w_apply, Period48.Realization.w_apply, map_smul, map_smul]
    congr 2
    change gramFactorLinearEquiv S factor
        (coefficientPhaseShift ((gramFactorLinearEquiv S factor).symm
          (gramFactorLinearEquiv S factor (WithLp.toLp 2 (Period48.Coefficient.nu i))))) =
      gramFactorLinearEquiv S factor (WithLp.toLp 2 (Period48.Coefficient.nu (i + 1)))
    rw [LinearEquiv.symm_apply_apply, coefficientPhaseShift_nu]

/-- The critical Gram cycle has an admissible multiplier factor, a nonzero
residual, and a strict second support block. -/
private lemma criticalCycle_strictificationInput
    (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
    (factor : S.transpose * S = Period48.gramMatrix) :
    0 < criticalFactor ∧ criticalFactor < 2 ∧
      IsProjectionCycle criticalFactor (Period48.Realization.eta S)
        (Period48.Realization.nu S criticalFactor) ∧
      (∃ i, ProjectionCycle.residual criticalFactor
          (Period48.Realization.nu S criticalFactor) i ≠ 0) ∧
      HasStrictBlock criticalFactor (Period48.Realization.eta S)
        (Period48.Realization.nu S criticalFactor) := by
  -- The threshold lemmas provide the scalar side conditions independently of
  -- the geometric certificate.
  have hγ : 0 < criticalFactor := criticalFactor_pos
  have hγtwo : criticalFactor < 2 := criticalFactor_lt_two
  -- The fixed-polytopes API supplies the cycle and its phase-independent
  -- positive residual at the endpoint.
  have hcycle := Period48.FixedPolytopes.isProjectionCycle S factor
    criticalFactor le_rfl
  obtain ⟨c_r, hc_r, hresidual⟩ :=
    Period48.FixedPolytopes.constantPositiveResidual S factor
      criticalFactor le_rfl
  have hnonzero : ∃ i, ProjectionCycle.residual criticalFactor
      (Period48.Realization.nu S criticalFactor) i ≠ 0 := by
    refine ⟨0, ?_⟩
    intro hzero
    have hnorm := hresidual 0
    rw [hzero, norm_zero] at hnorm
    linarith
  -- The second support table is strict at the critical factor, so it is a
  -- valid `HasStrictBlock` witness without any first-block strictness claim.
  have hstrict : HasStrictBlock criticalFactor
      (Period48.Realization.eta S)
      (Period48.Realization.nu S criticalFactor) := by
    right
    exact Period48.FixedPolytopes.secondSupports_strict S factor
  exact ⟨hγ, hγtwo, hcycle, hnonzero, hstrict⟩

/-- Coordinate padding preserves an orthogonal cyclic symmetry of two finite
Euclidean phase families. -/
private lemma hasOrthogonalCyclicSymmetry_comp_euclideanFinInclusion
    {N d n : ℕ} (hdn : d ≤ n)
    {eta nu : ZMod N → EuclideanSpace ℝ (Fin d)}
    (symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry eta nu) :
    ProjectionCycle.HasOrthogonalCyclicSymmetry
      (fun i ↦ euclideanFinInclusion hdn (eta i))
      (fun i ↦ euclideanFinInclusion hdn (nu i)) := by
  -- Conjugate the source symmetry to the range of the coordinate inclusion.
  obtain ⟨U, hU⟩ := symmetry
  let e := euclideanFinInclusion hdn
  let rangeAction : LinearMap.range e.toLinearMap →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    e.comp (U.toLinearIsometry.comp e.equivRange.symm.toLinearIsometry)
  -- Extend this range isometry to the ambient Euclidean space and upgrade it
  -- to an equivalence using finite-dimensional injective-surjective duality.
  let ambientAction : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n) := rangeAction.extend
  have ambientAction_surjective : Function.Surjective ambientAction := by
    exact LinearMap.surjective_of_injective ambientAction.injective
  let ambientEquiv : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.ofSurjective ambientAction ambientAction_surjective
  refine ⟨ambientEquiv, ?_⟩
  intro i
  obtain ⟨heta, hnu⟩ := hU i
  constructor
  · -- On an included phase vector, the ambient extension agrees with the
    -- conjugated source symmetry.
    change ambientEquiv (e (eta i)) = e (eta (i + 1))
    rw [LinearIsometryEquiv.coe_ofSurjective]
    have range_apply := LinearIsometry.extend_apply rangeAction (e.equivRange (eta i))
    simpa only [ambientAction, rangeAction, LinearIsometry.coe_comp,
      Function.comp_apply, LinearIsometry.equivRange_apply_coe,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply,
      heta] using range_apply
  · -- The same extension identity advances the multiplier family.
    change ambientEquiv (e (nu i)) = e (nu (i + 1))
    rw [LinearIsometryEquiv.coe_ofSurjective]
    have range_apply := LinearIsometry.extend_apply rangeAction (e.equivRange (nu i))
    simpa only [ambientAction, rangeAction, LinearIsometry.coe_comp,
      Function.comp_apply, LinearIsometry.equivRange_apply_coe,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply,
      hnu] using range_apply

/-- Strictification of the critical Gram cycle yields a nontrivial strict,
cyclically symmetric cycle in `EuclideanSpace ℝ (Fin 96)`. -/
private lemma criticalStrictCycle_exists :
    ∃ eta nu : ZMod 48 → EuclideanSpace ℝ (Fin 96),
      IsStrictProjectionCycle criticalFactor eta nu ∧
        (∃ i, ProjectionCycle.residual criticalFactor nu i ≠ 0) ∧
        ProjectionCycle.HasOrthogonalCyclicSymmetry eta nu := by
  -- Factor the positive Gram matrix and feed its endpoint certificate and
  -- cyclic symmetry to the generic strictification interface.
  obtain ⟨S, factor_source⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := Period48.gramMatrix)).mp
    Period48.FixedPolytopes.gramMatrix_posDef.posSemidef.nonneg
  have factor : S.transpose * S = Period48.gramMatrix := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using factor_source.symm
  obtain ⟨hγ, hγtwo, hcycle, hnonzero, hstrict⟩ :=
    criticalCycle_strictificationInput S factor
  obtain ⟨d, hd, eta, nu, hstrictCycle, hresidual, symmetry_preserved⟩ :=
    IsProjectionCycle.strictifyOneBlock criticalFactor
      (Period48.Realization.eta S)
      (Period48.Realization.nu S criticalFactor) (by norm_num) hγ hγtwo
      hcycle hnonzero hstrict
  have hd96 : d ≤ 96 := by
    simpa using hd
  have strict_symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry eta nu := by
    exact symmetry_preserved (criticalCycle_hasOrthogonalCyclicSymmetry S factor)
  let e := euclideanFinInclusion hd96
  let eta' : ZMod 48 → EuclideanSpace ℝ (Fin 96) := fun i ↦ e (eta i)
  let nu' : ZMod 48 → EuclideanSpace ℝ (Fin 96) := fun i ↦ e (nu i)
  have strict_cycle' : IsStrictProjectionCycle criticalFactor eta' nu' := by
    exact isStrictProjectionCycle_comp_linearIsometry e criticalFactor eta nu hstrictCycle
  have residual' : ∃ i, ProjectionCycle.residual criticalFactor nu' i ≠ 0 := by
    obtain ⟨i, hi⟩ := hresidual
    refine ⟨i, ?_⟩
    rw [projectionCycleResidual_comp_linearIsometry]
    simpa only [map_zero] using e.injective.ne hi
  have symmetry' : ProjectionCycle.HasOrthogonalCyclicSymmetry eta' nu' := by
    exact hasOrthogonalCyclicSymmetry_comp_euclideanFinInclusion hd96 strict_symmetry
  exact ⟨eta', nu', strict_cycle', residual', symmetry'⟩

/-- At `criticalFactor`, smooth strongly convex objectives on `ℝ⁹⁶` with
globally Lipschitz derivatives have a unique-update period-`48` trajectory of
constant positive objective value, while the origin is their unique primal
optimum of value zero and forms a KKT triple. -/
theorem smoothCounterexample :
    ∃ f g : EuclideanSpace ℝ (Fin 96) → ℝ,
      ∃ μf μg : ℝ, ∃ Lf Lg : NNReal,
      ∃ x y dual : ℕ → EuclideanSpace ℝ (Fin 96), ∃ c_f : ℝ,
        0 < μf ∧ 0 < μg ∧
        StrongConvexOn Set.univ μf f ∧ StrongConvexOn Set.univ μg g ∧
        ContDiff ℝ 1 f ∧ ContDiff ℝ 1 g ∧
        LipschitzWith Lf (fderiv ℝ f) ∧ LipschitzWith Lg (fderiv ℝ g) ∧
        IsTrajectory criticalFactor (ofReal f) (ofReal g) x y dual ∧
        HasUniqueUpdates (ofReal f) (ofReal g) x y dual ∧
        Function.Periodic (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) 48 ∧
        0 < c_f ∧ (∀ k, f (x (k + 1)) + g (y (k + 1)) = c_f) ∧
        IsKKT (ofReal f) (ofReal g) 0 0 0 ∧
        ofReal f 0 + ofReal g 0 = 0 ∧
        IsPrimalMinimizer (ofReal f) (ofReal g) 0 ∧
        ∀ z, IsPrimalMinimizer (ofReal f) (ofReal g) z → z = 0 := by
  -- The generic smooth realization preserves the strict cycle in its padded
  -- ambient dimension and gives the quantitative lower bound at the origin.
  obtain ⟨η, ν, hstrict, _, hsym⟩ := criticalStrictCycle_exists
  exact SmoothCycle.counterexample criticalFactor η ν criticalFactor_pos hstrict hsym

/-- Finite closed convex piecewise-quadratic objectives at `criticalFactor`
support a unique-update period-`48` trajectory with constant positive objective
value, while the origin is KKT and has optimal value zero. -/
theorem periodicPiecewiseQuadratic :
    ∃ f g : EuclideanSpace ℝ (Fin 96) → ℝ,
      ∃ x y dual : ℕ → EuclideanSpace ℝ (Fin 96), ∃ c_f : ℝ,
        IsFiniteClosedConvexPiecewiseQuadratic f ∧
        IsFiniteClosedConvexPiecewiseQuadratic g ∧
        IsTrajectory criticalFactor (ofReal f) (ofReal g) x y dual ∧
        HasUniqueUpdates (ofReal f) (ofReal g) x y dual ∧
        Function.Periodic (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) 48 ∧
        0 < c_f ∧ (∀ k, f (x (k + 1)) + g (y (k + 1)) = c_f) ∧
        IsKKT (ofReal f) (ofReal g) 0 0 0 ∧
        ofReal f 0 + ofReal g 0 = 0 ∧
        IsPrimalMinimizer (ofReal f) (ofReal g) 0 := by
  -- The strict cycle's active supporting forms give objectives that vanish at
  -- the origin and have a constant positive value along the prescribed orbit.
  obtain ⟨eta, nu, strict_cycle, _, symmetry⟩ := criticalStrictCycle_exists
  obtain ⟨first_symmetry, second_symmetry⟩ :=
    projectionCycleSupportFamilies_hasOrthogonalCyclicSymmetry
      criticalFactor eta nu symmetry
  obtain ⟨alphaX, alphaX_pos, selfX, activeX⟩ :=
    cyclicSupport_activeForm
      (ProjectionCycle.xVertex criticalFactor eta nu)
      (ProjectionCycle.firstNormal criticalFactor eta nu)
      strict_cycle.1 first_symmetry
  obtain ⟨alphaY, alphaY_pos, selfY, activeY⟩ :=
    cyclicSupport_activeForm eta (ProjectionCycle.secondNormal criticalFactor nu)
      strict_cycle.2 second_symmetry
  -- The max-square construction turns the two active cyclic families into
  -- fixed nonnegative piecewise-quadratic objectives.
  obtain ⟨f, f_piecewise, f_zero, f_nonneg, f_ray⟩ :=
    maxSquareObjective_spec
      (ProjectionCycle.xVertex criticalFactor eta nu)
      (ProjectionCycle.firstNormal criticalFactor eta nu)
      alphaX alphaX_pos selfX activeX
  obtain ⟨g, g_piecewise, g_zero, g_nonneg, g_ray⟩ :=
    maxSquareObjective_spec eta (ProjectionCycle.secondNormal criticalFactor nu)
      alphaY alphaY_pos selfY activeY
  have f_vertex (i : ZMod 48) :
      f (ProjectionCycle.xVertex criticalFactor eta nu i) = alphaX / 2 := by
    simpa only [one_smul, one_pow, one_mul] using (f_ray 1 zero_le_one i).1
  have g_vertex (i : ZMod 48) : g (eta i) = alphaY / 2 := by
    simpa only [one_smul, one_pow, one_mul] using (g_ray 1 zero_le_one i).1
  have first_supports (i : ZMod 48) (z : EuclideanSpace ℝ (Fin 96)) :
      f (ProjectionCycle.xVertex criticalFactor eta nu i) +
          inner ℝ (ProjectionCycle.firstNormal criticalFactor eta nu i)
            (z - ProjectionCycle.xVertex criticalFactor eta nu i) ≤ f z := by
    simpa only [one_smul] using (f_ray 1 zero_le_one i).2 z
  have second_supports (i : ZMod 48) (z : EuclideanSpace ℝ (Fin 96)) :
      g (eta i) + inner ℝ (ProjectionCycle.secondNormal criticalFactor nu i)
          (z - eta i) ≤ g z := by
    simpa only [one_smul] using (g_ray 1 zero_le_one i).2 z
  obtain ⟨trajectory, unique_updates⟩ := ofRealSupportedCycle_updates
    criticalFactor eta nu f g criticalFactor_pos first_supports second_supports
  have periodic : Function.Periodic
      (fun k ↦
        (ProjectionCycle.xSequence criticalFactor eta nu (k + 1),
          ProjectionCycle.ySequence eta (k + 1),
          ProjectionCycle.dualSequence nu (k + 1))) 48 := by
    intro k
    have phase_eq : ((k + 48 : ℕ) : ZMod 48) = (k : ZMod 48) := by
      simp only [Nat.cast_add, ZMod.natCast_self, add_zero]
    -- All three stored sequences read the same cyclic phase after 48 steps.
    simp only [ProjectionCycle.xSequence_succ, ProjectionCycle.ySequence_succ,
      ProjectionCycle.dualSequence_succ, phase_eq]
  let c_f := alphaX / 2 + alphaY / 2
  have objective_pos : 0 < c_f := by
    dsimp only [c_f]
    linarith
  have objective_value (k : ℕ) :
      f (ProjectionCycle.xSequence criticalFactor eta nu (k + 1)) +
          g (ProjectionCycle.ySequence eta (k + 1)) = c_f := by
    -- Successor evaluation exposes one phase, where both max-square values are
    -- the constant active self-products divided by two.
    simp only [ProjectionCycle.xSequence_succ, ProjectionCycle.ySequence_succ,
      f_vertex, g_vertex, c_f]
  obtain ⟨kkt, value, primal⟩ :=
    ofRealOriginOptimality f g f_zero g_zero f_nonneg g_nonneg
  exact ⟨f, g, ProjectionCycle.xSequence criticalFactor eta nu,
    ProjectionCycle.ySequence eta, ProjectionCycle.dualSequence nu, c_f,
    f_piecewise, g_piecewise, trajectory, unique_updates, periodic,
    objective_pos, objective_value, kkt, value, primal⟩

/-- Another pair of finite closed convex piecewise-quadratic objectives at
`criticalFactor` has uniquely attained ADMM updates whose residual and
objective values grow geometrically; the origin is KKT and has optimal value
zero. -/
theorem growingPiecewiseQuadratic :
    ∃ f g : EuclideanSpace ℝ (Fin 96) → ℝ,
      ∃ x y dual : ℕ → EuclideanSpace ℝ (Fin 96), ∃ c_r c_f κ : ℝ,
        IsFiniteClosedConvexPiecewiseQuadratic f ∧
        IsFiniteClosedConvexPiecewiseQuadratic g ∧
        IsTrajectory criticalFactor (ofReal f) (ofReal g) x y dual ∧
        HasUniqueUpdates (ofReal f) (ofReal g) x y dual ∧
        0 < c_r ∧ 0 < c_f ∧ 1 < κ ∧
        (∀ k, ‖x (k + 1) - y (k + 1)‖ = c_r * κ ^ k) ∧
        (∀ k, f (x (k + 1)) + g (y (k + 1)) = c_f * κ ^ (2 * k)) ∧
        IsKKT (ofReal f) (ofReal g) 0 0 0 ∧
        ofReal f 0 + ofReal g 0 = 0 ∧
        IsPrimalMinimizer (ofReal f) (ofReal g) 0 := by
  obtain ⟨η, ν, hstrict, hnonzero, hsym⟩ := criticalStrictCycle_exists
  exact GeometricGrowth.counterexample criticalFactor η ν criticalFactor_pos
    hstrict hnonzero hsym

end ConsensusADMM
