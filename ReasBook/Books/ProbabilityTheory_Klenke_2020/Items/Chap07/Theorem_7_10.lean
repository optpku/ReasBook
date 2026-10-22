/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Corollary_7_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function MeasureTheory Set EuclideanSpace
open scoped Topology

noncomputable section

universe u

variable {n : ℕ}
variable {G : Set (EuclideanSpace ℝ (Fin n))}
variable {φ : EuclideanSpace ℝ (Fin n) → ℝ}
local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩


/-- The Hessian matrix of `φ` on `G`, computed from the second derivative within `G`
in the standard basis of `ℝⁿ`. -/
def hessianMatrixWithin
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix₂
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (bilinearIteratedFDerivWithinTwo ℝ φ G x)

/-- Helper for Theorem 7.10: along a line through `x` in direction `v`, the first derivative of
the restricted one-dimensional function is the first Fréchet derivative applied to `v`. -/
lemma hasDerivAt_line_restriction
    (hG_open : IsOpen G) (hφ_c2 : ContDiffOn ℝ 2 φ G)
    {x v : EuclideanSpace ℝ (Fin n)} (hx : x ∈ G) :
    HasDerivAt (fun t : ℝ ↦ φ (x + t • v)) ((fderivWithin ℝ φ G x) v) 0 := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  -- The line map is differentiable, and the openness of `G` upgrades the within-derivative to an
  -- ordinary derivative near `x`.
  have hφ :
      HasFDerivWithinAt φ (fderivWithin ℝ φ G x) G (L 0 + x) := by
    simpa [L] using
      ((hφ_c2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)) x hx).hasFDerivWithinAt
  have hL : HasFDerivAt (fun t : ℝ ↦ L t + x) L 0 := by
    simpa [L] using (L.hasFDerivAt.add_const x)
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, L t + x ∈ G := by
    have hcont : Continuous fun t : ℝ ↦ L t + x := L.continuous.add continuous_const
    have hx' : L 0 + x ∈ G := by
      simpa [L] using hx
    simpa [L] using hcont.continuousAt.preimage_mem_nhds (hG_open.mem_nhds hx')
  -- The chain rule on the line restriction gives the required derivative formula.
  simpa [L, add_comm, add_left_comm, add_assoc] using hφ.comp_hasDerivAt 0 hL hmem

/-- Helper for Theorem 7.10: the second derivative of a line restriction is the second derivative
bilinear form evaluated twice on the direction vector. -/
lemma hasDerivAt_line_restriction_fderiv
    (hG_open : IsOpen G) (hφ_c2 : ContDiffOn ℝ 2 φ G)
    {x v : EuclideanSpace ℝ (Fin n)} (hx : x ∈ G) :
    HasDerivAt
      (fun t : ℝ ↦ (fderivWithin ℝ φ G (x + t • v)) v)
      (bilinearIteratedFDerivWithinTwo ℝ φ G x v v) 0 := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hφ₁ : ContDiffOn ℝ 1 (fderivWithin ℝ φ G) G := by
    simpa using
      hφ_c2.fderivWithin hG_open.uniqueDiffOn
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  -- Differentiate the map `y ↦ (fderivWithin φ G y) v`, then compose with the line.
  have hφ :
      HasFDerivWithinAt (fun y ↦ (fderivWithin ℝ φ G y) v)
        (((ContinuousLinearMap.apply ℝ ℝ v).comp
          (fderivWithin ℝ (fderivWithin ℝ φ G) G x))) G (L 0 + x) := by
    have hfd :
        HasFDerivWithinAt (fderivWithin ℝ φ G)
          (fderivWithin ℝ (fderivWithin ℝ φ G) G x) G (L 0 + x) := by
      simpa [L] using
        ((hφ₁.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) x hx).hasFDerivWithinAt
    simpa [Function.comp] using
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasFDerivWithinAt (L 0 + x) hfd
  have hL : HasFDerivAt (fun t : ℝ ↦ L t + x) L 0 := by
    simpa [L] using (L.hasFDerivAt.add_const x)
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, L t + x ∈ G := by
    have hcont : Continuous fun t : ℝ ↦ L t + x := L.continuous.add continuous_const
    have hx' : L 0 + x ∈ G := by
      simpa [L] using hx
    simpa [L] using hcont.continuousAt.preimage_mem_nhds (hG_open.mem_nhds hx')
  -- The resulting scalar derivative is exactly the bilinear form evaluated on `(v, v)`.
  simpa [L, bilinearIteratedFDerivWithinTwo, add_comm, add_left_comm, add_assoc] using
    hφ.comp_hasDerivAt 0 hL hmem

/-- Helper for Theorem 7.10: the strict epigraph of a convex function on an open convex domain is
open in the ambient product space. -/
lemma strict_epigraph_isOpen
    (hG_open : IsOpen G) (hφ : ConvexOn ℝ G φ) :
    IsOpen {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 ∈ G ∧ φ p.1 < p.2} := by
  have hcont : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦ φ p.1 - p.2)
      (G ×ˢ (Set.univ : Set ℝ)) := by
    -- Continuity on `G × ℝ` comes from continuity of `φ` on the open set `G`.
    have hφc : ContinuousOn φ G := hφ.continuousOn hG_open
    exact (hφc.comp continuous_fst.continuousOn fun _ hp ↦ hp.1).sub continuous_snd.continuousOn
  refine isOpen_iff_mem_nhds.2 ?_
  intro p hp
  have hpG : p ∈ G ×ˢ (Set.univ : Set ℝ) := by
    simpa using hp.1
  have hmem : {q : EuclideanSpace ℝ (Fin n) × ℝ | φ q.1 - q.2 < 0} ∈
      𝓝[ G ×ˢ (Set.univ : Set ℝ)] p := by
    -- The inequality `φ p.1 < p.2` is exactly `F p < 0`, so continuity gives a neighborhood
    -- where the same strict inequality persists.
    have : φ p.1 - p.2 ∈ Set.Iio 0 := by
      simpa [sub_lt_iff_lt_add] using hp.2
    exact (hcont p hpG).preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds this)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hmem with ⟨u, hu, huF⟩
  have hu' : u ∩ (G ×ˢ (Set.univ : Set ℝ)) ∈ 𝓝 p := by
    exact inter_mem hu ((hG_open.prod isOpen_univ).mem_nhds hpG)
  exact mem_of_superset hu' fun q hq ↦
    ⟨hq.2.1, by simpa [sub_lt_iff_lt_add] using huF ⟨hq.1, hq.2⟩⟩

/-- Helper for Theorem 7.10: a strict separator of the graph point from the strict epigraph
normalizes to a touching supporting affine minorant on `G`. -/
lemma supporting_affine_map_of_strict_epigraph_separator
    (x₀ : G)
    (L : StrongDual ℝ (EuclideanSpace ℝ (Fin n) × ℝ))
    (hsep : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ,
      p.1 ∈ G ∧ φ p.1 < p.2 → L ((x₀ : EuclideanSpace ℝ (Fin n)), φ x₀) < L p) :
    ∃ g ∈ supporting_affine_maps_on G φ, g x₀ = φ x₀ := by
  let u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    L.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  let α : ℝ := L (0, 1)
  have hdecomp (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
      L (z, t) = u z + t * α := by
    rw [show (z, t) = (z, 0) + (0, t) by simp, map_add]
    rw [show L (0, t) = t * α by
      rw [show ((0 : EuclideanSpace ℝ (Fin n)), t) =
          t • ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) by simp, map_smul]
      simp [α, smul_eq_mul]]
    simp [u]
  have hα_pos : 0 < α := by
    -- Testing the separator on the vertical ray above `((x₀ : E), φ x₀)` forces the `ℝ`-part of
    -- the functional to be strictly positive.
    have h := hsep ((x₀ : EuclideanSpace ℝ (Fin n)), φ x₀ + 1) ⟨x₀.2, by linarith⟩
    rw [hdecomp, hdecomp] at h
    linarith
  have hle : ∀ y : G, -α⁻¹ * u y + (φ x₀ + α⁻¹ * u x₀) ≤ φ y := by
    intro y
    by_contra hy
    have hforall : ∀ ε > 0, -α⁻¹ * u y + (φ x₀ + α⁻¹ * u x₀) < φ y + ε := by
      intro ε hε
      -- Evaluating the separator on points just above `(y, φ y)` yields the desired affine
      -- inequality after dividing by the positive coefficient `α`.
      have h := hsep (y, φ y + ε) ⟨y.2, by linarith⟩
      rw [hdecomp, hdecomp] at h
      have hα_ne : α ≠ 0 := ne_of_gt hα_pos
      have : -α⁻¹ * u y + (φ x₀ + α⁻¹ * u x₀) < φ y + ε := by
        field_simp [hα_ne]
        linarith
      exact this
    have hε : 0 < (-α⁻¹ * u y + (φ x₀ + α⁻¹ * u x₀) - φ y) / 2 := by
      linarith
    have := hforall _ hε
    linarith
  let l : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := ((-α⁻¹) • u : _ →L[ℝ] ℝ)
  refine ⟨Set.restrict G l + const G (φ x₀ + α⁻¹ * u x₀), ?_, ?_⟩
  · -- The normalized affine map stays below `φ` on `G`.
    refine mem_supporting_affine_maps_on_iff.2 ?_
    refine ⟨?_, l, φ x₀ + α⁻¹ * u x₀, rfl⟩
    intro y
    simpa [l] using hle y
  · -- The affine map was normalized to touch `φ` at `x₀`.
    change l x₀ + (φ x₀ + α⁻¹ * u x₀) = φ x₀
    simp [l]

/-- Helper for Theorem 7.10: convexity on an open convex subset of `ℝⁿ` yields a touching
supporting affine minorant at every point. -/
lemma exists_supporting_affine_minorant_of_convexOn
    (hG_open : IsOpen G) (hφ : ConvexOn ℝ G φ) :
    ∀ x₀ : G, ∃ g ∈ supporting_affine_maps_on G φ, g x₀ = φ x₀ := by
  intro x₀
  let A : Set (EuclideanSpace ℝ (Fin n) × ℝ) := {p | p.1 ∈ G ∧ φ p.1 < p.2}
  have hA_convex : Convex ℝ A := by
    simpa [A] using hφ.convex_strict_epigraph
  have hA_open : IsOpen A := by
    simpa [A] using strict_epigraph_isOpen hG_open hφ
  have hx₀_not_mem : ((x₀ : EuclideanSpace ℝ (Fin n)), φ x₀) ∉ A := by
    simp [A]
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open hA_convex hA_open hx₀_not_mem
  -- Route correction: use strict-epigraph separation directly, then normalize the separator into
  -- the required supporting affine minorant.
  exact supporting_affine_map_of_strict_epigraph_separator x₀ L
    (fun p hp ↦ hL p (by simpa [A] using hp))

/-- Helper for Theorem 7.10: restricting a convex function to an affine line preserves convexity on
the line preimage of the domain. -/
lemma line_preimage_convexOn
    (hφ : ConvexOn ℝ G φ) (x v : EuclideanSpace ℝ (Fin n)) :
    ConvexOn ℝ {t : ℝ | x + t • v ∈ G} (fun t : ℝ ↦ φ (x + t • v)) := by
  let γ : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x (x + v)
  -- The affine line `t ↦ x + t • v` is an affine precomposition of `φ`.
  convert hφ.comp_affineMap γ using 1 <;>
    ext t <;>
    simp [γ, AffineMap.lineMap_apply_module', sub_eq_add_neg, add_comm]

/-- Helper for Theorem 7.10: the second derivative bilinear form on an open set is symmetric. -/
lemma secondDerivativeBilinWithin_isSymm
    (hG_open : IsOpen G) (hφ_c2 : ContDiffOn ℝ 2 φ G)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ G) :
    (bilinearIteratedFDerivWithinTwo ℝ φ G x).IsSymm := by
  rw [LinearMap.isSymm_def]
  intro v w
  have hsymm :=
    (hφ_c2 x hx).isSymmSndFDerivWithinAt (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
      (hG_open.uniqueDiffOn) (by simpa [hG_open.interior_eq] using subset_closure hx) hx
  -- Symmetry of the iterated Fréchet derivative specializes to symmetry of the associated bilinear
  -- form on pairs of directions.
  have hswap :
      iteratedFDerivWithin ℝ 2 φ G x ![v, w] =
        iteratedFDerivWithin ℝ 2 φ G x ![w, v] :=
    hsymm.iteratedFDerivWithin_cons (hG_open.uniqueDiffOn) hx
  rw [iteratedFDerivWithin_two_apply' φ (hG_open.uniqueDiffOn) hx v w,
    iteratedFDerivWithin_two_apply' φ (hG_open.uniqueDiffOn) hx w v] at hswap
  simpa [bilinearIteratedFDerivWithinTwo] using hswap

/-- Helper for Theorem 7.10: the derivative formula for the line restriction holds at every
parameter value, not only at `0`. -/
lemma hasDerivAt_line_restriction_at
    (hG_open : IsOpen G) (hφ_c2 : ContDiffOn ℝ 2 φ G)
    {x v : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : x + t • v ∈ G) :
    HasDerivAt (fun s : ℝ ↦ φ (x + s • v)) ((fderivWithin ℝ φ G (x + t • v)) v) t := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hφ :
      HasFDerivWithinAt φ (fderivWithin ℝ φ G (x + t • v)) G (L t + x) := by
    simpa [L, add_comm, add_left_comm, add_assoc] using
      ((hφ_c2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)) (x + t • v) ht).hasFDerivWithinAt
  have hL : HasFDerivAt (fun s : ℝ ↦ L s + x) L t := by
    simpa [L] using (L.hasFDerivAt.add_const x)
  have hmem : ∀ᶠ s : ℝ in 𝓝 t, L s + x ∈ G := by
    have hcont : Continuous fun s : ℝ ↦ L s + x := L.continuous.add continuous_const
    have ht' : L t + x ∈ G := by
      simpa [L, add_comm, add_left_comm, add_assoc] using ht
    simpa [L, add_comm, add_left_comm, add_assoc] using
      hcont.continuousAt.preimage_mem_nhds (hG_open.mem_nhds ht')
  -- Apply the chain rule to the affine line map at the parameter `t`.
  simpa [L, add_comm, add_left_comm, add_assoc] using hφ.comp_hasDerivAt t hL hmem

/-- Helper for Theorem 7.10: along an affine line, the derivative of the first-derivative formula
recovers the quadratic form of the second derivative at every parameter value. -/
lemma hasDerivAt_line_restriction_fderiv_at
    (hG_open : IsOpen G) (hφ_c2 : ContDiffOn ℝ 2 φ G)
    {x v : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : x + t • v ∈ G) :
    HasDerivAt (fun s : ℝ ↦ (fderivWithin ℝ φ G (x + s • v)) v)
      (bilinearIteratedFDerivWithinTwo ℝ φ G (x + t • v) v v) t := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hφ₁ : ContDiffOn ℝ 1 (fderivWithin ℝ φ G) G := by
    simpa using
      hφ_c2.fderivWithin hG_open.uniqueDiffOn
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hφ :
      HasFDerivWithinAt (fun y ↦ (fderivWithin ℝ φ G y) v)
        (((ContinuousLinearMap.apply ℝ ℝ v).comp
          (fderivWithin ℝ (fderivWithin ℝ φ G) G (x + t • v)))) G (L t + x) := by
    have hfd :
        HasFDerivWithinAt (fderivWithin ℝ φ G)
          (fderivWithin ℝ (fderivWithin ℝ φ G) G (x + t • v)) G (L t + x) := by
      simpa [L, add_comm, add_left_comm, add_assoc] using
        ((hφ₁.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) (x + t • v) ht).hasFDerivWithinAt
    simpa [Function.comp] using
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasFDerivWithinAt (L t + x) hfd
  have hL : HasFDerivAt (fun s : ℝ ↦ L s + x) L t := by
    simpa [L] using (L.hasFDerivAt.add_const x)
  have hmem : ∀ᶠ s : ℝ in 𝓝 t, L s + x ∈ G := by
    have hcont : Continuous fun s : ℝ ↦ L s + x := L.continuous.add continuous_const
    have ht' : L t + x ∈ G := by
      simpa [L, add_comm, add_left_comm, add_assoc] using ht
    simpa [L, add_comm, add_left_comm, add_assoc] using
      hcont.continuousAt.preimage_mem_nhds (hG_open.mem_nhds ht')
  -- Differentiate the first-derivative expression once more along the same affine line.
  simpa [L, bilinearIteratedFDerivWithinTwo, add_comm, add_left_comm, add_assoc] using
    hφ.comp_hasDerivAt t hL hmem

-- Proof sketch: use the finite-dimensional supporting-hyperplane theorem on open convex subsets
-- of `ℝⁿ`, then repeat the supremum and countable-approximation arguments from Corollary 7.8 with
-- affine functionals on `ℝⁿ` in place of affine functions on an interval.
/-- Theorem 7.10 (1): On an open convex subset `G ⊆ ℝⁿ`, the equivalent characterizations from
Corollary 7.8 remain valid with `G` in place of the interval `I`: convexity, existence of a
supporting affine minorant at each point, representation as the supremum of all supporting affine
minorants, and approximation by partial pointwise maxima of a sequence of supporting affine
minorants. -/
theorem convexOn_tfae_supporting_affine_minorants_open_convex
    (hG_open : IsOpen G) (hG_convex : Convex ℝ G) :
    List.TFAE
      [ConvexOn ℝ G φ,
        ∀ x₀ : G, ∃ g ∈ supporting_affine_maps_on G φ, g x₀ = φ x₀,
        (supporting_affine_maps_on G φ).Nonempty ∧
          sSup (supporting_affine_maps_on G φ) = Set.restrict G φ,
        ∃ g : ℕ → G → ℝ,
          (∀ m, g m ∈ supporting_affine_maps_on G φ) ∧
            ∀ x : G, Tendsto (fun m ↦ partial_max g m x) atTop (𝓝 (φ x))] := by
  classical
  tfae_have 1 → 2 := by
    intro hφ
    -- Route correction: obtain the supporting affine minorant from strict-epigraph separation on
    -- `G × ℝ`, then normalize the separator into the required affine witness.
    exact exists_supporting_affine_minorant_of_convexOn hG_open hφ
  tfae_have 2 → 3 := by
    intro hcontact
    -- Touching minorants at every point force the support family to recover `φ` by pointwise `sSup`.
    have hsupport :
        (∀ hcontact : ∀ x₀ : G, ∃ g ∈ supporting_affine_maps_on G φ, g x₀ = φ x₀,
          (supporting_affine_maps_on G φ).Nonempty ∧
            sSup (supporting_affine_maps_on G φ) = Set.restrict G φ) :=
      fun hcontact ↦ supporting_affine_maps_nonempty_and_sSup_eq_of_forall_contact hcontact
    exact hsupport hcontact
  tfae_have 3 → 4 := by
    intro hsup
    -- First extract a countable supporting family with the same supremum, then use monotone
    -- convergence of the partial maxima.
    have hIsLUB : IsLUB (supporting_affine_maps_on G φ) (Set.restrict G φ) := by
      rw [← hsup.2]
      refine isLUB_csSup hsup.1 ?_
      exact ⟨Set.restrict G φ, fun h hh y ↦ hh.1 y⟩
    have hnat :
        (supporting_affine_maps_on G φ).Nonempty →
          IsLUB (supporting_affine_maps_on G φ) (Set.restrict G φ) →
            ∃ g : ℕ → G → ℝ, (∀ n, g n ∈ supporting_affine_maps_on G φ) ∧
              (⨆ n, g n) = Set.restrict G φ :=
      fun hne hIsLUB ↦ exists_nat_supporting_affine_family_of_isLUB hne hIsLUB
    obtain ⟨g, hg, hgSup⟩ := hnat hsup.1 hIsLUB
    refine ⟨g, hg, ?_⟩
    intro x
    have hbddg : BddAbove (Set.range (fun n ↦ g n x)) := by
      refine ⟨φ x, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (hg n).1 x
    have hlim := partial_max_tendsto_iSup g x hbddg
    have hxSup : (⨆ n, g n x) = φ x := by
      simpa using congrFun hgSup x
    simpa [hxSup] using hlim
  tfae_have 4 → 3 := by
    intro hseq
    rcases hseq with ⟨g, hg, hconv⟩
    refine ⟨⟨g 0, hg 0⟩, ?_⟩
    ext x
    apply le_antisymm
    · -- Every supporting affine minorant lies below `φ`, so the support envelope does as well.
      rw [sSup_apply_eq_sSup_image]
      exact csSup_le (image_nonempty.mpr ⟨g 0, hg 0⟩) fun z hz ↦ by
        rcases hz with ⟨f, hf, rfl⟩
        exact hf.1 x
    · -- Each partial maximum stays below the support envelope; passing to the limit yields equality.
      have hEvalBdd : BddAbove (Function.eval x '' supporting_affine_maps_on G φ) := by
        refine ⟨φ x, ?_⟩
        rintro _ ⟨f, hf, rfl⟩
        exact hf.1 x
      have hle_support : ∀ n, g n x ≤ sSup (supporting_affine_maps_on G φ) x := by
        intro n
        rw [sSup_apply_eq_sSup_image]
        exact le_csSup hEvalBdd ⟨g n, hg n, rfl⟩
      have hpartial_le : ∀ n, partial_max g n x ≤ sSup (supporting_affine_maps_on G φ) x := by
        intro n
        induction n with
        | zero =>
            simpa [partial_max_zero] using hle_support 0
        | succ n ihn =>
            rw [partial_max_succ]
            exact max_le ihn (hle_support (n + 1))
      have hsSup_tendsto :
          Filter.Tendsto (fun _ : ℕ ↦ sSup (supporting_affine_maps_on G φ) x) Filter.atTop
            (𝓝 (sSup (supporting_affine_maps_on G φ) x)) := tendsto_const_nhds
      have hle := le_of_tendsto_of_tendsto' (hconv x) hsSup_tendsto hpartial_le
      simpa using hle
  tfae_have 3 → 1 := by
    intro hsup
    rw [ConvexOn]
    refine ⟨hG_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    have hz_mem : a • x + b • y ∈ G := by
      simpa using hG_convex hx hy ha hb hab
    let z : G := ⟨a • x + b • y, hz_mem⟩
    have hz_eq : sSup (supporting_affine_maps_on G φ) z = φ (a • x + b • y) := by
      simpa [z] using congrFun hsup.2 z
    have hsSup_le :
        sSup (supporting_affine_maps_on G φ) z ≤ a * φ x + b * φ y := by
      rw [sSup_apply_eq_sSup_image]
      refine csSup_le (image_nonempty.mpr hsup.1) ?_
      rintro _ ⟨g, hg, rfl⟩
      rcases mem_supporting_affine_maps_on_iff.mp hg with ⟨hminor, l, c, rfl⟩
      have hx_le : l x + c ≤ φ x := by
        simpa using hminor ⟨x, hx⟩
      have hy_le : l y + c ≤ φ y := by
        simpa using hminor ⟨y, hy⟩
      have h_aff : l (a • x + b • y) + c = a * (l x + c) + b * (l y + c) := by
        have hl : l (a • x + b • y) = a * l x + b * l y := by
          calc
            l (a • x + b • y) = l (a • x) + l (b • y) := by rw [map_add]
            _ = a • l x + b • l y := by rw [l.map_smul, l.map_smul]
            _ = a * l x + b * l y := by simp [smul_eq_mul]
        have hc : c = a * c + b * c := by
          have hmul := congrArg (fun r : ℝ ↦ c * r) hab
          simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using hmul.symm
        have hsum : a * (l x + c) + b * (l y + c) = a * l x + b * l y + c := by
          calc
            a * (l x + c) + b * (l y + c) = a * l x + b * l y + (a * c + b * c) := by ring
            _ = a * l x + b * l y + c := by rw [← hc]
        calc
          l (a • x + b • y) + c = a * l x + b * l y + c := by rw [hl]
          _ = a * (l x + c) + b * (l y + c) := hsum.symm
      have hineq : l (a • x + b • y) + c ≤ a * φ x + b * φ y := by
        rw [h_aff]
        nlinarith
      simpa [z] using hineq
    exact hz_eq.symm ▸ hsSup_le
  tfae_finish

/- Theorem 7.10 (2): The textbook continuity statement on open convex subsets of `ℝⁿ`
is the finite-dimensional specialization of the canonical mathlib theorem
`ConvexOn.continuousOn`. -/
recall ConvexOn.continuousOn {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
  {f : E → ℝ} [FiniteDimensional ℝ E] (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
  ContinuousOn f C

-- Proof sketch: restrict the continuous function from Theorem 7.10 (2) to the subtype `G`
-- and use continuity-implies-measurability for maps between Borel spaces.
/-- Theorem 7.10 (3): A convex real-valued function on an open convex subset of `ℝⁿ`
is measurable for the subspace Borel structure on that set. -/
theorem convexOn_subtype_measurable_open_convex
    (hG_open : IsOpen G) (hφ : ConvexOn ℝ G φ) :
    Measurable (Set.restrict G φ) := by
  exact (continuousOn_iff_continuous_restrict.1 (hφ.continuousOn hG_open)).measurable

-- Proof sketch: for the forward implication, restrict `φ` to every line segment in `G` and apply
-- the one-dimensional second-derivative criterion. For the converse, positivity of the Hessian in
-- every direction gives nonnegative second directional derivatives along line segments, which
-- yields convexity.
/-- Theorem 7.10 (4): If `φ` is twice continuously differentiable on an open convex subset
`G ⊆ ℝⁿ`, then `φ` is convex on `G` exactly when its Hessian matrix on `G`
is positive semidefinite at every point of `G`. -/
theorem convexOn_iff_hessianMatrixWithin_posSemidef
    (hG_open : IsOpen G) (hG_convex : Convex ℝ G) (hφ_c2 : ContDiffOn ℝ 2 φ G) :
    ConvexOn ℝ G φ ↔
      ∀ x ∈ G, (hessianMatrixWithin φ G x).PosSemidef := by
  constructor
  · intro hφ x hx
    have hB : (bilinearIteratedFDerivWithinTwo ℝ φ G x).IsPosSemidef := by
      refine LinearMap.isPosSemidef_def.2 ?_
      refine ⟨secondDerivativeBilinWithin_isSymm hG_open hφ_c2 x hx, ?_⟩
      rw [LinearMap.isNonneg_def]
      intro v
      let D : Set ℝ := {t : ℝ | x + t • v ∈ G}
      let k : ℝ → ℝ := fun t ↦ (fderivWithin ℝ φ G (x + t • v)) v
      have hconv : ConvexOn ℝ D (fun t : ℝ ↦ φ (x + t • v)) :=
        line_preimage_convexOn hφ x v
      have hD_open : IsOpen D := by
        let γ : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x (x + v)
        convert hG_open.preimage γ.continuous_of_finiteDimensional using 1 <;>
          ext t <;>
          simp [D, γ, AffineMap.lineMap_apply_module', sub_eq_add_neg, add_comm]
      have hD0 : (0 : ℝ) ∈ D := by
        simpa [D]
      have hmono : MonotoneOn k D := by
        intro s hs t ht hst
        have hs_eq : k s = deriv (fun u : ℝ ↦ φ (x + u • v)) s := by
          symm
          exact (hasDerivAt_line_restriction_at hG_open hφ_c2 hs).deriv
        have ht_eq : k t = deriv (fun u : ℝ ↦ φ (x + u • v)) t := by
          symm
          exact (hasDerivAt_line_restriction_at hG_open hφ_c2 ht).deriv
        rw [hs_eq, ht_eq]
        exact hconv.monotoneOn_deriv
          (fun u hu ↦
            (hasDerivAt_line_restriction_at hG_open hφ_c2 hu).differentiableAt)
          hs ht hst
      -- A monotone first-derivative field has nonnegative derivative, which is exactly the
      -- quadratic form of the second derivative in direction `v`.
      have hnonneg : 0 ≤ derivWithin k D 0 := hmono.derivWithin_nonneg
      have hk : derivWithin k D 0 = bilinearIteratedFDerivWithinTwo ℝ φ G x v v := by
        have hderiv :
            HasDerivWithinAt k (bilinearIteratedFDerivWithinTwo ℝ φ G x v v) D 0 :=
          by
            have hderivAt :=
              hasDerivAt_line_restriction_fderiv_at hG_open hφ_c2 hD0
            have hderivWithin :
                HasDerivWithinAt
                  (fun s : ℝ ↦ (fderivWithin ℝ φ G (x + s • v)) v)
                  (bilinearIteratedFDerivWithinTwo ℝ φ G x v v) D 0 :=
              by
                simpa [zero_smul] using hderivAt.hasDerivWithinAt
            simpa [k, D, zero_smul] using
              hderivWithin
        exact hderiv.derivWithin (hD_open.uniqueDiffWithinAt hD0)
      simpa [D, k] using hnonneg.trans_eq hk
    -- Transport positive semidefiniteness from the bilinear second derivative to its matrix in the
    -- standard basis.
    simpa [hessianMatrixWithin] using
      (LinearMap.isPosSemidef_iff_posSemidef_toMatrix
        ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)).mp hB
  · intro hH
    rw [ConvexOn]
    refine ⟨hG_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    let v : EuclideanSpace ℝ (Fin n) := y - x
    let D : Set ℝ := {t : ℝ | x + t • v ∈ G}
    let g : ℝ → ℝ := fun t ↦ φ (x + t • v)
    let g' : ℝ → ℝ := fun t ↦ (fderivWithin ℝ φ G (x + t • v)) v
    let g'' : ℝ → ℝ := fun t ↦ bilinearIteratedFDerivWithinTwo ℝ φ G (x + t • v) v v
    have hD_convex : Convex ℝ D := by
      let γ : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x (x + v)
      convert hG_convex.affine_preimage γ using 1 <;>
        ext t <;>
        simp [D, γ, AffineMap.lineMap_apply_module', sub_eq_add_neg, add_comm]
    have hD0 : (0 : ℝ) ∈ D := by
      simpa [D, v]
    have hD1 : (1 : ℝ) ∈ D := by
      simpa [D, v]
    have hD_open : IsOpen D := by
      let γ : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x (x + v)
      convert hG_open.preimage γ.continuous_of_finiteDimensional using 1 <;>
        ext t <;>
        simp [D, γ, AffineMap.lineMap_apply_module', sub_eq_add_neg, add_comm]
    have hD_int : interior D = D := interior_eq_iff_isOpen.mpr hD_open
    have convexOn_of_line_second_derivative_nonneg :
        ∀ (f' f'' : ℝ → ℝ), ContinuousOn g D →
          (∀ t ∈ interior D, HasDerivWithinAt g (f' t) (interior D) t) →
          (∀ t ∈ interior D, HasDerivWithinAt f' (f'' t) (interior D) t) →
          (∀ t ∈ interior D, 0 ≤ f'' t) →
          ConvexOn ℝ D g := by
      intro f' f'' hg_cont hf' hf'' hf''₀
      exact convexOn_of_hasDerivWithinAt2_nonneg hD_convex hg_cont hf' hf'' hf''₀
    have hg_convex : ConvexOn ℝ D g := by
      refine convexOn_of_line_second_derivative_nonneg g' g'' ?_ ?_ ?_ ?_
      · -- The line restriction is continuous on its natural domain.
        have hφ_cont : ContinuousOn φ G := hφ_c2.continuousOn
        exact hφ_cont.comp
          (show ContinuousOn (fun t : ℝ ↦ x + t • v) D by fun_prop)
          fun _ ht ↦ ht
      · -- The first derivative of the line restriction is given by the ambient Fréchet derivative.
        intro t ht
        have htD : t ∈ D := by
          simpa [hD_int] using ht
        simpa [g', g, D, v] using
          (hasDerivAt_line_restriction_at hG_open hφ_c2 htD).hasDerivWithinAt
      · -- Differentiating once more yields the quadratic form of the second derivative.
        intro t ht
        have htD : t ∈ D := by
          simpa [hD_int] using ht
        have hderivAt :=
          hasDerivAt_line_restriction_fderiv_at hG_open hφ_c2 htD
        have hderivWithin :
            HasDerivWithinAt
              (fun s : ℝ ↦ (fderivWithin ℝ φ G (x + s • v)) v)
              (bilinearIteratedFDerivWithinTwo ℝ φ G (x + t • v) v v)
              D t :=
          hderivAt.hasDerivWithinAt
        simpa [g'', g', D, v, hD_int] using
          hderivWithin
      · intro t ht
        have htD : t ∈ D := by
          simpa [hD_int] using ht
        have hm :
            (LinearMap.toMatrix₂
              (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
              (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
              (bilinearIteratedFDerivWithinTwo ℝ φ G (x + t • v))).PosSemidef := by
          simpa [hessianMatrixWithin] using
            hH (x + t • v) htD
        have hB : (bilinearIteratedFDerivWithinTwo ℝ φ G (x + t • v)).IsPosSemidef :=
          (LinearMap.isPosSemidef_iff_posSemidef_toMatrix
            ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)).2 hm
        -- Positive semidefiniteness of the Hessian matrix gives nonnegative second directional
        -- derivatives along the line.
        simpa [g''] using hB.isNonneg.nonneg v
    have hineq : φ (x + b • v) ≤ a * φ x + b * φ y := by
      simpa [g, v, smul_eq_mul] using hg_convex.2 hD0 hD1 ha hb hab
    -- Evaluate the convexity inequality for the line restriction at the parameter `b`, where
    -- `x + b • (y - x) = a • x + b • y`.
    have hb_eq : x + b • v = a • x + b • y := by
      ext i
      have hab' : a = 1 - b := by
        linarith
      rw [hab']
      simp [v, sub_eq_add_neg]
      ring
    exact hb_eq.symm ▸ hineq
