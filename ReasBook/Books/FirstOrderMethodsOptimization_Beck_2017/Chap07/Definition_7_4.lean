/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Function

section

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 7.4 is `source-facing`: the primitive data are a one-variable profile and the
factorization `f = g ∘ norm`. Domain sampling against the Chapter 2 properness owner
`IsProperExtendedRealFunction`, the Chapter 7 coordinate owner `Function.IsAbsolutelySymmetric`,
the Euclidean orthogonal-symmetry owner `IsSymmetricFunction`, and mathlib's real-normed-space
radius-realization owner `exists_norm_eq` shows the following split.

The owner split is therefore:
- `source-facing`: norm dependence via a one-variable proper profile,
- `core/canonical`: composition with `norm` on a normed additive ambient space,
- `bridge/view`: the Euclidean orthogonal-invariance characterization via `IsSymmetricFunction`.

Properness of the ambient function is derived from the profile together with realization of
nonnegative radii, so it should not remain parallel primitive data in the owner itself. -/

/-- Definition 7.4: an extended-real-valued function on a normed additive space is
norm-dependent when it factors through the ambient norm via a proper one-variable profile,
canonically extended by `⊤` on the negative ray. For `E = EuclideanSpace ℝ (Fin n)`, this is the
textbook notion on `ℝ^n`. -/
class IsNormDependent (f : E → EReal) : Prop where
  profile_exists :
    ∃ g : ℝ → EReal,
          IsProperExtendedRealFunction g ∧
        (∀ t : ℝ, t < 0 → g t = ⊤) ∧
          f = g ∘ norm

/-- A function is norm-dependent exactly when it admits a proper scalar profile on `ℝ` that equals
`⊤` on the negative ray and recovers the function by composition with the ambient norm. -/
theorem isNormDependent_iff_exists_profile (f : E → EReal) :
    IsNormDependent f ↔
      ∃ g : ℝ → EReal,
        IsProperExtendedRealFunction g ∧
          (∀ t : ℝ, t < 0 → g t = ⊤) ∧
            f = g ∘ norm := by
  constructor
  · intro hf
    exact hf.profile_exists
  · intro hf
    exact ⟨hf⟩

/-- The constant zero extended-real-valued function is norm-dependent. -/
instance : IsNormDependent (fun _ : E ↦ (0 : EReal)) := by
  refine ⟨?_⟩
  -- Use the explicit scalar profile that is finite on the nonnegative ray and `⊤` on negatives.
  refine ⟨fun t ↦ if t < 0 then ⊤ else 0, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- The profile never takes the value `-∞`.
      intro t
      by_cases ht : t < 0
      · simp [ht]
      · simp [ht]
    · -- Radius `0` is in the effective domain.
      refine ⟨0, ?_⟩
      simp [effective_domain]
  · -- By construction the profile is `⊤` on the negative ray.
    intro t ht
    simp [ht]
  · -- On norms, the profile reduces to the constant value `0`.
    funext x
    simp [Function.comp_apply, norm_nonneg]

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- A norm-dependent function is proper because its scalar profile is proper and agrees with the
function on the nonnegative norm ray. -/
theorem IsNormDependent.isProper {f : E → EReal} (hf : IsNormDependent f) :
    IsProperExtendedRealFunction f := by
  rcases hf.profile_exists with ⟨g, hgProper, hg_neg, rfl⟩
  refine ⟨?_, ?_⟩
  · -- The ambient function never takes the value `-∞` because the scalar profile does not.
    intro x
    simpa [Function.comp_apply] using hgProper.ne_bot ‖x‖
  · -- A finite profile value occurs at some nonnegative radius, which we realize in the ambient
    -- space via `exists_norm_eq`.
    rcases hgProper.effective_domain_nonempty with ⟨r, hr⟩
    have hr_nonneg : 0 ≤ r := by
      by_contra hr_nonneg
      have htop : g r = ⊤ := hg_neg r (lt_of_not_ge hr_nonneg)
      simpa [effective_domain, htop] using hr
    rcases exists_norm_eq E hr_nonneg with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [effective_domain, Function.comp_apply, hx] using hr

/-- A norm-dependent function is proper. -/
instance (f : E → EReal) [hf : IsNormDependent f] : IsProperExtendedRealFunction f :=
  hf.isProper

end

section

open WithLp

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable [Nonempty ι]

local notation "E" => EuclideanSpace ℝ ι

/-- Helper for Definition 7.4: an orthogonal matrix preserves the Euclidean norm of the associated
coordinate vector. -/
lemma norm_toLp_orthogonalGroup_smul (A : Matrix.orthogonalGroup ι ℝ) (x : ι → ℝ) :
    ‖toLp 2 (A • x)‖ = ‖toLp 2 x‖ := by
  -- Compare squared norms and rewrite them as dot products of the coordinate vectors.
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, (A • x) i ^ 2 = dotProduct (A • x) (A • x) := by
      unfold dotProduct
      simp [sq]
    _ = dotProduct x x := by
      -- Orthogonality gives `Aᵀ * A = 1`, so the quadratic form is unchanged.
      change dotProduct (((A : Matrix ι ι ℝ).mulVec x)) (((A : Matrix ι ι ℝ).mulVec x)) =
        dotProduct x x
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
        (Matrix.mem_orthogonalGroup_iff' ι ℝ).1 A.2, Matrix.vecMul_one]
    _ = ∑ i, x i ^ 2 := by
      unfold dotProduct
      simp [sq]

/-- Helper for Definition 7.4: every Euclidean vector is the orthogonal image of a one-coordinate
representative with the same norm. -/
lemma exists_orthogonalGroup_smul_single_of_norm_eq (i0 : ι) (x : E) :
    ∃ A : Matrix.orthogonalGroup ι ℝ, toLp 2 (A • (Pi.single i0 ‖x‖ : ι → ℝ)) = x := by
  classical
  by_cases hx : x = 0
  · -- The zero vector is already the image of the zero radius under the identity matrix.
    refine ⟨1, ?_⟩
    simp [hx]
  · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let v : ι → E := fun _ ↦ ‖x‖⁻¹ • x
    have hv : Orthonormal ℝ (({i0} : Set ι).restrict v) := by
      refine ⟨?_, ?_⟩
      · -- The distinguished vector is normalized to have norm `1`.
        intro i
        rcases i with ⟨i, hi⟩
        simp only [Set.mem_singleton_iff] at hi
        subst i
        change ‖v i0‖ = 1
        dsimp [v]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        field_simp [hnorm]
      · -- A singleton family is automatically pairwise orthogonal.
        intro i j hij
        rcases i with ⟨i, hi⟩
        rcases j with ⟨j, hj⟩
        simp only [Set.mem_singleton_iff] at hi hj
        subst i
        subst j
        exact (hij rfl).elim
    have hcard : Module.finrank ℝ E = Fintype.card ι := finrank_euclideanSpace (𝕜 := ℝ) (ι := ι)
    obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
    let A : Matrix.orthogonalGroup ι ℝ :=
      ⟨(EuclideanSpace.basisFun ι ℝ).toBasis.toMatrix b.toBasis,
        (EuclideanSpace.basisFun ι ℝ).toMatrix_orthonormalBasis_mem_orthogonal b⟩
    refine ⟨A, ?_⟩
    ext i
    have hb_i0 : b i0 = ‖x‖⁻¹ • x := hb i0 (by simp)
    -- Expand the distinguished column of the orthogonal matrix and simplify the scaling.
    change (((A : Matrix ι ι ℝ).mulVec (Pi.single i0 ‖x‖ : ι → ℝ)) i) = x i
    simp [A, Matrix.mulVec_single, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr,
      hb_i0]
    field_simp [hnorm]

/-- Helper for Definition 7.4: orthogonal symmetry makes the function constant on Euclidean
spheres. -/
lemma eq_of_same_norm_of_isSymmetricFunction {f : E → EReal} (i0 : ι)
    (hsym : IsSymmetricFunction Set.univ (f ∘ toLp 2)) {x y : E} (hxy : ‖x‖ = ‖y‖) :
    f x = f y := by
  rcases exists_orthogonalGroup_smul_single_of_norm_eq i0 x with ⟨A, hA⟩
  rcases exists_orthogonalGroup_smul_single_of_norm_eq i0 y with ⟨B, hB⟩
  -- Move both points to the same radius representative and use orthogonal invariance there.
  calc
    f x = (f ∘ toLp 2) (A • (Pi.single i0 ‖x‖ : ι → ℝ)) := by
      simpa [Function.comp_apply] using congrArg f hA.symm
    _ = (f ∘ toLp 2) (Pi.single i0 ‖x‖ : ι → ℝ) := by
      simpa using hsym.map_smul A (by simp) _
    _ = (f ∘ toLp 2) (Pi.single i0 ‖y‖ : ι → ℝ) := by
      simp [hxy]
    _ = (f ∘ toLp 2) (B • (Pi.single i0 ‖y‖ : ι → ℝ)) := by
      simpa using (hsym.map_smul B (by simp) _).symm
    _ = f y := by
      simpa [Function.comp_apply] using congrArg f hB

-- Proof sketch: for the forward implication, use orthogonal invariance and the transitive action
-- of the orthogonal group on each Euclidean sphere to show that `f` depends only on `‖x‖`; then
-- take that radial profile as `g`, extended by `⊤` on the negative ray. For the reverse
-- implication, `f = g ∘ norm` is unchanged by an orthogonal matrix because orthogonal maps
-- preserve the Euclidean norm. The chapter owner `IsSymmetricFunction` lives on the coordinate
-- model `ι → ℝ`, so we compare with the pullback `f ∘ toLp 2`.
/-- On `EuclideanSpace ℝ ι`, a proper extended-real-valued function is norm-dependent exactly
when its pullback along the canonical coordinate map `toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι` is
symmetric with respect to the full orthogonal group, equivalently invariant under every
orthogonal matrix on the coordinate model. For `ι = Fin n`, this is the textbook characterization
on `ℝ^n`. -/
theorem isNormDependent_iff_isSymmetricFunction (f : E → EReal) :
    IsNormDependent f ↔ IsSymmetricFunction Set.univ (f ∘ toLp 2) := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  constructor
  · intro hf
    rcases hf.profile_exists with ⟨g, hgProper, hg_neg, hfg⟩
    refine
      { toIsProperExtendedRealFunction := ?_
        map_smul := ?_ }
    · refine ⟨?_, ?_⟩
      · -- Properness of `f ∘ toLp 2` inherits pointwise from the scalar profile.
        intro x
        simpa [hfg, Function.comp_apply] using hgProper.ne_bot ‖toLp 2 x‖
      · -- Realize a finite profile radius by a single-coordinate vector.
        rcases hgProper.effective_domain_nonempty with ⟨r, hr⟩
        have hr_nonneg : 0 ≤ r := by
          by_contra hr_nonneg
          have htop : g r = ⊤ := hg_neg r (lt_of_not_ge hr_nonneg)
          simpa [effective_domain, htop] using hr
        refine ⟨Pi.single i0 r, ?_⟩
        simpa [effective_domain, Function.comp_apply, hfg, Real.norm_of_nonneg hr_nonneg] using hr
    · intro A hA x
      -- Orthogonal matrices preserve the Euclidean norm, so the profile value is unchanged.
      rw [hfg]
      simp only [Function.comp_apply]
      congr 1
      exact norm_toLp_orthogonalGroup_smul A x
  · intro hsym
    refine ⟨?_⟩
    refine ⟨fun t ↦ if t < 0 then ⊤ else f (toLp 2 (Pi.single i0 t)), ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · -- The constructed radial profile never attains `-∞`.
        intro t
        by_cases ht : t < 0
        · simp [ht]
        · have hne : f (toLp 2 (Pi.single i0 t : ι → ℝ)) ≠ ⊥ := hsym.ne_bot _
          simpa [ht] using hne
      · -- Use any finite point of `f ∘ toLp 2` and replace it by the radius representative with
        -- the same norm.
        rcases hsym.effective_domain_nonempty with ⟨u, hu⟩
        refine ⟨‖toLp 2 u‖, ?_⟩
        have hnonneg : ¬‖toLp 2 u‖ < 0 := not_lt.mpr (norm_nonneg _)
        have hsame :
            f (toLp 2 (Pi.single i0 ‖toLp 2 u‖ : ι → ℝ)) = f (toLp 2 u) :=
          eq_of_same_norm_of_isSymmetricFunction i0 hsym
            (x := toLp 2 (Pi.single i0 ‖toLp 2 u‖ : ι → ℝ)) (y := toLp 2 u)
            (by
              simpa using
                PiLp.norm_toLp_single (p := 2) (β := fun _ : ι ↦ ℝ) i0 ‖toLp 2 u‖)
        have hu_fin : f (toLp 2 u) < ⊤ := by
          simpa [effective_domain, Function.comp_apply] using hu
        have hrep_fin : f (toLp 2 (Pi.single i0 ‖toLp 2 u‖ : ι → ℝ)) < ⊤ := by
          rwa [hsame]
        simpa [effective_domain, hnonneg] using hrep_fin
    · -- By definition the profile is `⊤` on the negative ray.
      intro t ht
      simp [ht]
    · -- Evaluate the radial profile at `‖x‖` and compare with `f x` using sphere transitivity.
      funext x
      have hnonneg : ¬‖x‖ < 0 := not_lt.mpr (norm_nonneg _)
      have hsame :
          f (toLp 2 (Pi.single i0 ‖x‖ : ι → ℝ)) = f x :=
        eq_of_same_norm_of_isSymmetricFunction i0 hsym
          (x := toLp 2 (Pi.single i0 ‖x‖ : ι → ℝ)) (y := x)
          (by
            simpa using
              PiLp.norm_toLp_single (p := 2) (β := fun _ : ι ↦ ℝ) i0 ‖x‖)
      simpa [Function.comp_apply, hnonneg] using hsame.symm

end

end Function
