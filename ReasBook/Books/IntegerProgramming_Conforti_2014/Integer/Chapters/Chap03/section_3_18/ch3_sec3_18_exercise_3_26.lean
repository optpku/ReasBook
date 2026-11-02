import Mathlib

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the statement
-- below is written against mathlib's canonical `Convex`, `IsClosed`, and `IsBounded` APIs.

-- Declarations for this item will be appended below by the statement pipeline.

section ContainsRay

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A subset of a real vector space contains a ray if it contains all nonnegative points on some
affine ray with nonzero direction. -/
def ContainsRay (S : Set E) : Prop :=
  ∃ x d : E, d ≠ 0 ∧ ∀ t : ℝ, 0 ≤ t → x + t • d ∈ S

end ContainsRay

section AsymptoticCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedAddTorsor E E := by
  infer_instance

local instance : AddTorsor E E := by
  infer_instance

local instance : IsTopologicalAddGroup E := by
  infer_instance

local instance : IsTopologicalAddTorsor E := by
  infer_instance

/-- Helper for Exercise 3.26: a contained affine ray yields an asymptotic direction. -/
lemma mem_asymptoticCone_of_forall_nonneg_add_smul_mem
    {S : Set E} {x d : E}
    (h : ∀ t : ℝ, 0 ≤ t → x + t • d ∈ S) :
    d ∈ (asymptoticCone ℝ S : Set E) := by
  -- The ray parameterization tends to the asymptotic-neighborhood filter of its direction.
  rw [mem_asymptoticCone_iff]
  have hTendstoBase :
      Filter.Tendsto (fun t : ℝ ↦ t • d) Filter.atTop
        ((AffineSpace.asymptoticNhds ℝ E d : Filter E)) := by
    simpa using
      Filter.tendsto_id.atTop_smul_const_tendsto_asymptoticNhds d
  have hTendsto :
      Filter.Tendsto (fun t : ℝ ↦ t • d + x) Filter.atTop
        ((AffineSpace.asymptoticNhds ℝ E d : Filter E)) := by
    simpa [vadd_eq_add] using
      hTendstoBase.asymptoticNhds_vadd_const x
  have hEventually : ∀ᶠ t : ℝ in Filter.atTop, t • d + x ∈ S := by
    -- Along `atTop`, the ray-membership hypothesis is eventually available because `t` is
    -- eventually nonnegative.
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simpa [add_comm] using h t ht
  -- Along `atTop`, the ray-membership hypothesis is eventually available because `t` is eventually
  -- nonnegative.
  exact hTendsto.frequently (Filter.Eventually.frequently hEventually)

/-- Helper for Exercise 3.26: a nonzero asymptotic direction of a closed convex set generates a
contained ray. -/
lemma containsRay_of_ne_zero_mem_asymptoticCone
    {S : Set E} (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    {d : E} (hd0 : d ≠ 0) (hd : d ∈ (asymptoticCone ℝ S : Set E)) :
    ContainsRay S := by
  -- Any nonempty asymptotic cone gives a base point of `S`, from which the convex-closed API
  -- extends the whole ray in direction `d`.
  rcases asymptoticCone_nonempty.mp ⟨d, hd⟩ with ⟨x, hx⟩
  refine ⟨x, d, hd0, ?_⟩
  intro t ht
  -- Closed convexity upgrades the asymptotic direction into actual ray containment from `x`.
  simpa [vadd_eq_add, add_comm] using
    hS_convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hS_closed ht hd hx

/-- Helper for Exercise 3.26: for a closed convex set, containing a ray is equivalent to having a
nonzero asymptotic direction. -/
lemma containsRay_iff_exists_ne_zero_mem_asymptoticCone
    {S : Set E} (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) :
    ContainsRay S ↔ ∃ d : E, d ≠ 0 ∧ d ∈ (asymptoticCone ℝ S : Set E) := by
  constructor
  · intro hRay
    rcases hRay with ⟨x, d, hd0, hxd⟩
    -- A contained affine ray directly provides the corresponding asymptotic direction.
    exact ⟨d, hd0, mem_asymptoticCone_of_forall_nonneg_add_smul_mem hxd⟩
  · intro hCone
    rcases hCone with ⟨d, hd0, hd⟩
    -- Conversely, a nonzero asymptotic direction yields a contained ray by closed convexity.
    exact containsRay_of_ne_zero_mem_asymptoticCone hS_closed hS_convex hd0 hd

variable [FiniteDimensional ℝ E]

/-- Exercise 3.26. A closed convex set in a finite-dimensional real normed space is bounded if and
only if it contains no ray. -/
theorem closed_convex_isBounded_iff_not_containsRay
    {S : Set E} (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) :
    Bornology.IsBounded S ↔ ¬ ContainsRay S := by
  constructor
  · intro hBounded hRay
    -- A bounded set has only the zero asymptotic direction, so it cannot contain a genuine ray.
    rcases (containsRay_iff_exists_ne_zero_mem_asymptoticCone hS_closed hS_convex).mp hRay with
      ⟨d, hd0, hd⟩
    have hsingleton := asymptoticCone_subset_singleton_of_bounded hBounded hd
    exact hd0 (by simpa using hsingleton)
  · intro hNoRay
    by_contra hUnbounded
    -- An unbounded closed convex set has a nonzero asymptotic direction, hence contains a ray.
    have hCone : ∃ d : E, d ≠ 0 ∧ d ∈ (asymptoticCone ℝ S : Set E) :=
      not_bounded_iff_exists_ne_zero_mem_asymptoticCone.mp hUnbounded
    rcases hCone with
      ⟨d, hd0, hd⟩
    exact hNoRay <| (containsRay_iff_exists_ne_zero_mem_asymptoticCone hS_closed hS_convex).mpr
      ⟨d, hd0, hd⟩

end AsymptoticCone
