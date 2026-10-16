module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

universe u v

noncomputable section

/-- The input families and positive factor defining a finite cyclic ADMM configuration. -/
structure CycleConfig (N : ℕ) (E : Type u) [AddCommGroup E] [Module ℝ E] where
  eta : Fin N → E
  nu : Fin N → E
  gamma : ℝ
  two_le : 2 ≤ N
  gamma_pos : 0 < gamma

namespace CycleConfig

/-- Construct a cyclic configuration from its two vector families and positive factor. -/
def ofFamilies {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (eta nu : Fin N → E) (gamma : ℝ) (two_le : 2 ≤ N) (gamma_pos : 0 < gamma) :
    CycleConfig N E :=
  { eta := eta
    nu := nu
    gamma := gamma
    two_le := two_le
    gamma_pos := gamma_pos }

/-- The first family of a configuration constructed by `ofFamilies`. -/
theorem ofFamilies_eta {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (eta nu : Fin N → E) (gamma : ℝ) (two_le : 2 ≤ N) (gamma_pos : 0 < gamma) :
    (ofFamilies eta nu gamma two_le gamma_pos).eta = eta := by
  -- Reduce the first projection of the configuration constructor.
  rfl

/-- The second family of a configuration constructed by `ofFamilies`. -/
theorem ofFamilies_nu {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (eta nu : Fin N → E) (gamma : ℝ) (two_le : 2 ≤ N) (gamma_pos : 0 < gamma) :
    (ofFamilies eta nu gamma two_le gamma_pos).nu = nu := by
  -- Reduce the second projection of the configuration constructor.
  rfl

/-- The factor of a configuration constructed by `ofFamilies`. -/
theorem ofFamilies_gamma {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (eta nu : Fin N → E) (gamma : ℝ) (two_le : 2 ≤ N) (gamma_pos : 0 < gamma) :
    (ofFamilies eta nu gamma two_le gamma_pos).gamma = gamma := by
  -- Reduce the scalar projection of the configuration constructor.
  rfl

/-- The predecessor of a phase index, with indexing taken modulo `N`. -/
def previous {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) : Fin N :=
  ⟨(i.val + N - 1) % N,
    Nat.mod_lt _ (lt_of_lt_of_le (Nat.zero_lt_succ 1) q.two_le)⟩

/-- The value of the cyclic predecessor is `(i.val + N - 1) % N`. -/
theorem previous_val {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) :
    (q.previous i).val = (i.val + N - 1) % N := by
  -- Read the value field of the cyclic predecessor.
  rfl

/-- The multiplier residual `ρᵢ = γ⁻¹ • (νᵢ - νᵢ₋₁)`. -/
def residual {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) : E :=
  q.gamma⁻¹ • (q.nu i - q.nu (q.previous i))

/-- Evaluation formula for the multiplier residual. -/
theorem residual_apply {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) :
    q.residual i = q.gamma⁻¹ • (q.nu i - q.nu (q.previous i)) := by
  -- Unfold the residual at the chosen phase.
  rfl

/-- The first projection-cycle vertex `ξᵢ = ηᵢ + ρᵢ`. -/
def xVertex {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) : E :=
  q.eta i + q.residual i

/-- Evaluation formula for the first projection-cycle vertex. -/
theorem xVertex_apply {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) :
    q.xVertex i = q.eta i + q.residual i := by
  -- Unfold the first vertex at the chosen phase.
  rfl

/-- The first supporting normal `aᵢ = ηᵢ₋₁ - νᵢ₋₁ - ξᵢ`. -/
def xNormal {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) : E :=
  q.eta (q.previous i) - q.nu (q.previous i) - q.xVertex i

/-- Evaluation formula for the first supporting normal. -/
theorem xNormal_apply {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) :
    q.xNormal i = q.eta (q.previous i) - q.nu (q.previous i) - q.xVertex i := by
  -- Unfold the first supporting normal at the chosen phase.
  rfl

/-- The second supporting normal `cᵢ = νᵢ₋₁ + ρᵢ`. -/
def yNormal {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) : E :=
  q.nu (q.previous i) + q.residual i

/-- Evaluation formula for the second supporting normal. -/
theorem yNormal_apply {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) :
    q.yNormal i = q.nu (q.previous i) + q.residual i := by
  -- Unfold the second supporting normal at the chosen phase.
  rfl

end CycleConfig

namespace ProjectionCycle

/-- The origin together with all phase vertices other than the one indexed by `i`. -/
def nonselfVertices {N : ℕ} {E : Type u} [Zero E] (v : Fin N → E) (i : Fin N) : Set E :=
  {0} ∪ {z | ∃ j, j ≠ i ∧ z = v j}

/-- Membership in `nonselfVertices` means being the origin or a distinct phase vertex. -/
theorem mem_nonselfVertices {N : ℕ} {E : Type u} [Zero E] {v : Fin N → E}
    {i : Fin N} {z : E} :
    z ∈ nonselfVertices v i ↔ z = 0 ∨ ∃ j, j ≠ i ∧ z = v j := by
  -- Normalize membership in the union, singleton, and set comprehension.
  simp only [nonselfVertices, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]

end ProjectionCycle

namespace CycleConfig

/-- Transport a cyclic configuration through a real linear map. -/
def map {N : ℕ} {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (q : CycleConfig N E) (L : E →ₗ[ℝ] F) :
    CycleConfig N F :=
  { eta := fun i ↦ L (q.eta i)
    nu := fun i ↦ L (q.nu i)
    gamma := q.gamma
    two_le := q.two_le
    gamma_pos := q.gamma_pos }

/-- Mapping a cyclic configuration preserves the predecessor of every phase. -/
theorem map_previous {N : ℕ} {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (q : CycleConfig N E) (L : E →ₗ[ℝ] F) (i : Fin N) :
    (q.map L).previous i = q.previous i := by
  -- Compare the underlying phase indices; both use the same modular predecessor formula.
  ext
  rfl

/-- A linear map carries the residual family to the residual family of the mapped configuration. -/
theorem map_residual {N : ℕ} {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (q : CycleConfig N E) (L : E →ₗ[ℝ] F) (i : Fin N) :
    (q.map L).residual i = L (q.residual i) := by
  -- Move the linear map through the residual after identifying its predecessor.
  rw [residual_apply, residual_apply, map_previous, LinearMap.map_smul, LinearMap.map_sub]
  rfl

/-- A linear map carries the first vertex family to that of the mapped configuration. -/
theorem map_xVertex {N : ℕ} {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (q : CycleConfig N E) (L : E →ₗ[ℝ] F) (i : Fin N) :
    (q.map L).xVertex i = L (q.xVertex i) := by
  -- Transport the two vertex summands, using naturality of the residual.
  rw [xVertex_apply, xVertex_apply, map_residual, LinearMap.map_add]
  rfl

/-- A linear map carries the first normal family to that of the mapped configuration. -/
theorem map_xNormal {N : ℕ} {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (q : CycleConfig N E) (L : E →ₗ[ℝ] F) (i : Fin N) :
    (q.map L).xNormal i = L (q.xNormal i) := by
  -- Transport the normal's two differences, using naturality of the vertex.
  rw [xNormal_apply, xNormal_apply, map_previous, map_xVertex,
    LinearMap.map_sub, LinearMap.map_sub]
  rfl

/-- A linear map carries the second normal family to that of the mapped configuration. -/
theorem map_yNormal {N : ℕ} {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (q : CycleConfig N E) (L : E →ₗ[ℝ] F) (i : Fin N) :
    (q.map L).yNormal i = L (q.yNormal i) := by
  -- Transport the normal's two summands, using naturality of the residual.
  rw [yNormal_apply, yNormal_apply, map_previous, map_residual, LinearMap.map_add]
  rfl

/-- The four families derived from a cyclic configuration satisfy their defining formulas. -/
theorem cycleData_spec {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (q : CycleConfig N E) (i : Fin N) :
    q.residual i = q.gamma⁻¹ • (q.nu i - q.nu (q.previous i)) ∧
      q.xVertex i = q.eta i + q.residual i ∧
        q.xNormal i = q.eta (q.previous i) - q.nu (q.previous i) - q.xVertex i ∧
          q.yNormal i = q.nu (q.previous i) + q.residual i := by
  -- Assemble the four public evaluation laws without unfolding their definitions again.
  exact ⟨residual_apply q i, xVertex_apply q i, xNormal_apply q i, yNormal_apply q i⟩

end CycleConfig

namespace ProjectionCycle

/-- The multiplier residual `ρᵢ = γ⁻¹ • (νᵢ - νᵢ₋₁)` of cyclic data. -/
def residual {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (ν : ZMod N → E) (i : ZMod N) : E :=
  γ⁻¹ • (ν i - ν (i - 1))

/-- Evaluation formula for the multiplier residual. -/
theorem residual_apply {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (ν : ZMod N → E) (i : ZMod N) :
    residual γ ν i = γ⁻¹ • (ν i - ν (i - 1)) := by
  rfl

/-- The first projection-cycle vertex `ξᵢ = ηᵢ + ρᵢ`. -/
def xVertex {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (i : ZMod N) : E :=
  η i + residual γ ν i

/-- Evaluation formula for the first projection-cycle vertex. -/
theorem xVertex_apply {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (i : ZMod N) :
    xVertex γ η ν i = η i + residual γ ν i := by
  rfl

/-- The first supporting normal `aᵢ = ηᵢ₋₁ - νᵢ₋₁ - ξᵢ`. -/
def firstNormal {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (i : ZMod N) : E :=
  η (i - 1) - ν (i - 1) - xVertex γ η ν i

/-- Evaluation formula for the first supporting normal. -/
theorem firstNormal_apply {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (i : ZMod N) :
    firstNormal γ η ν i = η (i - 1) - ν (i - 1) - xVertex γ η ν i := by
  -- Expose the defining expression for the first supporting normal.
  rfl

/-- The second supporting normal `cᵢ = νᵢ₋₁ + ρᵢ`. -/
def secondNormal {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (ν : ZMod N → E) (i : ZMod N) : E :=
  ν (i - 1) + residual γ ν i

/-- Evaluation formula for the second supporting normal. -/
theorem secondNormal_apply {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (ν : ZMod N → E) (i : ZMod N) :
    secondNormal γ ν i = ν (i - 1) + residual γ ν i := by
  -- Expose the defining expression for the second supporting normal.
  rfl

/-- The origin and every phase vertex other than `p i` are supported at `p i`
by the normal `n i`. -/
def NonselfSupports {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p n : ZMod N → E) : Prop :=
  ∀ i, 0 ≤ inner ℝ (n i) (p i) ∧
    ∀ j, j ≠ i → 0 ≤ inner ℝ (n i) (p i - p j)

/-- Nonself support is support against the origin and every distinct phase vertex. -/
theorem nonselfSupports_iff {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p n : ZMod N → E} :
    NonselfSupports p n ↔
      ∀ i, 0 ≤ inner ℝ (n i) (p i) ∧
        ∀ j, j ≠ i → 0 ≤ inner ℝ (n i) (p i - p j) := by
  -- Unfold the support predicate to its origin and nonself inequalities.
  rfl

/-- The convex hull of the origin and the first-block cycle vertices. -/
def xSet {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) : Set E :=
  convexHull ℝ (Set.insert 0 (Set.range (xVertex γ η ν)))

/-- The first cycle set is the convex hull of the origin and the `xVertex` range. -/
theorem xSet_def {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) :
    xSet γ η ν = convexHull ℝ (Set.insert 0 (Set.range (xVertex γ η ν))) := by
  -- Expose the convex-hull definition of the first cycle set.
  rfl

/-- The convex hull of the origin and the second-block cycle vertices. -/
def ySet {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (η : ZMod N → E) : Set E :=
  convexHull ℝ (Set.insert 0 (Set.range η))

/-- The second cycle set is the convex hull of the origin and the `η` range. -/
theorem ySet_def {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (η : ZMod N → E) :
    ySet η = convexHull ℝ (Set.insert 0 (Set.range η)) := by
  -- Expose the convex-hull definition of the second cycle set.
  rfl

/-- The prescribed first-block sequence, shifted so update `k + 1` has phase `k`. -/
def xSequence {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (k : ℕ) : E :=
  xVertex γ η ν ((k : ZMod N) - 1)

/-- Evaluation of the prescribed first-block sequence. -/
theorem xSequence_apply {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (k : ℕ) :
    xSequence γ η ν k = xVertex γ η ν ((k : ZMod N) - 1) := by
  -- Evaluate the prescribed first-block sequence at its shifted phase.
  rfl

/-- The first-block value after update `k` is the phase-`k` vertex. -/
theorem xSequence_succ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (k : ℕ) :
    xSequence γ η ν (k + 1) = xVertex γ η ν (k : ZMod N) := by
  -- The successor cast contributes one, which cancels the phase shift.
  simp only [xSequence_apply, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

/-- The prescribed second-block sequence, initialized at the predecessor phase. -/
def ySequence {N : ℕ} {E : Type u} (η : ZMod N → E) (k : ℕ) : E :=
  η ((k : ZMod N) - 1)

/-- Evaluation of the prescribed second-block sequence. -/
theorem ySequence_apply {N : ℕ} {E : Type u} (η : ZMod N → E) (k : ℕ) :
    ySequence η k = η ((k : ZMod N) - 1) := by
  -- Evaluate the prescribed second-block sequence at its shifted phase.
  rfl

/-- The second-block sequence starts at the predecessor of phase zero. -/
theorem ySequence_zero {N : ℕ} {E : Type u} (η : ZMod N → E) :
    ySequence η 0 = η (-1) := by
  -- At time zero, the shifted phase is the predecessor of zero.
  simp only [ySequence_apply, Nat.cast_zero, zero_sub]

/-- The second-block value after update `k` is the phase-`k` vertex. -/
theorem ySequence_succ {N : ℕ} {E : Type u} (η : ZMod N → E) (k : ℕ) :
    ySequence η (k + 1) = η (k : ZMod N) := by
  -- The successor cast contributes one, which cancels the phase shift.
  simp only [ySequence_apply, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

/-- The prescribed multiplier sequence, initialized at the predecessor phase. -/
def dualSequence {N : ℕ} {E : Type u} (ν : ZMod N → E) (k : ℕ) : E :=
  ν ((k : ZMod N) - 1)

/-- Evaluation of the prescribed multiplier sequence. -/
theorem dualSequence_apply {N : ℕ} {E : Type u} (ν : ZMod N → E) (k : ℕ) :
    dualSequence ν k = ν ((k : ZMod N) - 1) := by
  -- Evaluate the prescribed multiplier sequence at its shifted phase.
  rfl

/-- The multiplier sequence starts at the predecessor phase of zero. -/
theorem dualSequence_zero {N : ℕ} {E : Type u} (ν : ZMod N → E) :
    dualSequence ν 0 = ν (-1) := by
  -- At time zero, the shifted multiplier phase is the predecessor of zero.
  simp only [dualSequence_apply, Nat.cast_zero, zero_sub]

/-- The multiplier after update `k` is the phase-`k` value. -/
theorem dualSequence_succ {N : ℕ} {E : Type u} (ν : ZMod N → E) (k : ℕ) :
    dualSequence ν (k + 1) = ν (k : ZMod N) := by
  -- The successor cast contributes one, which cancels the multiplier phase shift.
  simp only [dualSequence_apply, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

/-- The primal residual sequence of the prescribed post-update trajectory. -/
def primalResidual {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (k : ℕ) : E :=
  xSequence γ η ν (k + 1) - ySequence η (k + 1)

/-- The primal residual at time `k` is the configured residual at phase `k`. -/
theorem primalResidual_apply {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) (k : ℕ) :
    primalResidual γ η ν k = residual γ ν (k : ZMod N) := by
  -- Normalize both post-update sequences to phase `k`, then cancel the common vertex.
  simp only [primalResidual, xSequence_succ, ySequence_succ, xVertex_apply,
    add_sub_cancel_left]

end ProjectionCycle

/-- The two nonself-support families defining a projection cycle. -/
def IsProjectionCycle {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) : Prop :=
  ProjectionCycle.NonselfSupports (ProjectionCycle.xVertex γ η ν)
      (ProjectionCycle.firstNormal γ η ν) ∧
    ProjectionCycle.NonselfSupports η (ProjectionCycle.secondNormal γ ν)

/-- A projection cycle is exactly the pair of first- and second-block support families. -/
theorem isProjectionCycle_iff {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : ℝ} {η ν : ZMod N → E} :
    IsProjectionCycle γ η ν ↔
      ProjectionCycle.NonselfSupports (ProjectionCycle.xVertex γ η ν)
          (ProjectionCycle.firstNormal γ η ν) ∧
        ProjectionCycle.NonselfSupports η (ProjectionCycle.secondNormal γ ν) := by
  -- Expose the two support families bundled by the projection-cycle predicate.
  rfl

end

end ConsensusADMM
