/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Real.Sign
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.UrysohnsLemma

public section

noncomputable section

namespace VariationalRegularization

/-- `C2BoundaryIn Ω E` packages a source-faithful `C²` boundary presentation of
`frontier E` in `Ω` by a regular defining function. -/
structure C2BoundaryIn
    {d : ℕ}
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))
    (E : Set (EuclideanSpace ℝ (Fin d))) where
  definingFunction : EuclideanSpace ℝ (Fin d) → ℝ
  contDiffOn_definingFunction : ContDiffOn ℝ 2 definingFunction (Ω : Set (EuclideanSpace ℝ (Fin d)))
  frontier_eq_zeroSet :
    frontier E =
      {x | x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧ definingFunction x = 0}
  interior_eq_nonpos :
    E = {x | x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧ definingFunction x ≤ 0}
  regular_on_frontier :
    ∀ x ∈ frontier E, fderiv ℝ definingFunction x ≠ 0

/-- `IsOutwardUnitNormalIn Ω E h_boundary n` records that `n` is the outward
unit normal field attached to the `C²` boundary datum `h_boundary`. -/
structure IsOutwardUnitNormalIn
    {d : ℕ}
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))
    (E : Set (EuclideanSpace ℝ (Fin d)))
    (h_boundary : C2BoundaryIn Ω E)
    (n : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop where
  contDiffOn_normal : ContDiffOn ℝ 1 n (frontier E)
  norm_eq_one : ∀ x ∈ frontier E, ‖n x‖ = 1
  gradient_eq_pos_smul :
    ∀ x ∈ frontier E, ∃ c : ℝ, 0 < c ∧ gradient h_boundary.definingFunction x = c • n x

/-- `HasC2BoundaryIn Ω E` is the source-facing geometric hypothesis from
Example 8.12: the frontier `frontier E` is a `C²` boundary in `Ω` equipped
with the actual outward unit normal field coming from the defining function. -/
structure HasC2BoundaryIn
    {d : ℕ}
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))
    (E : Set (EuclideanSpace ℝ (Fin d))) where
  boundary : C2BoundaryIn Ω E
  outwardNormal : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  isOutwardNormal : IsOutwardUnitNormalIn Ω E boundary outwardNormal

/-- Package a `C²` boundary datum together with its outward unit normal field. -/
def HasC2BoundaryIn.ofBoundaryAndNormal
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (boundary : C2BoundaryIn Ω E)
    (outwardNormal : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (isOutwardNormal : IsOutwardUnitNormalIn Ω E boundary outwardNormal) :
    HasC2BoundaryIn Ω E :=
  ⟨boundary, outwardNormal, isOutwardNormal⟩

namespace HasC2BoundaryIn

/-- Helper for Example 8.12: the zero admissible field has zero divergence. -/
@[simp] lemma admissibleDivergence_zero
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence (AdmissibleTestField.zero Ω) x = 0 := by
  -- Rewrite the derivative of the zero field and collapse the coordinate sum.
  have hzero :
      fderiv ℝ (⇑(0 : TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1)) x = 0 := by
    change
      fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin d) => (0 : EuclideanSpace ℝ (Fin d))) x = 0
    simp
  rw [admissibleDivergence_def, AdmissibleTestField.zero_toTestFunction, hzero]
  simp

/-- Helper for Example 8.12: total variation is nonnegative because the zero
admissible field contributes the value `0`. -/
lemma totalVariation_nonneg
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    (0 : EReal) ≤ totalVariation f := by
  -- The zero admissible field witnesses a nonnegative element in the defining supremum.
  rw [totalVariation_def]
  refine le_sSup ?_
  refine ⟨AdmissibleTestField.zero Ω, by
    simp [admissibleDivergencePairing_def, admissibleDivergence_zero]⟩

/-- A packaged `C²` boundary presentation forces `E` to lie inside `Ω`. -/
theorem subset
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E) :
    E ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
  intro x hx
  rw [h_boundary.boundary.interior_eq_nonpos] at hx
  exact hx.1

/-- A packaged `C²` boundary presentation forces `frontier E` to lie inside `Ω`. -/
theorem frontier_subset
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E) :
    frontier E ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
  intro x hx
  rw [h_boundary.boundary.frontier_eq_zeroSet] at hx
  exact hx.1

/-- Helper for Example 8.12: in dimension `0`, the regularity clause forces the
frontier to be empty. -/
lemma frontier_eq_empty_of_zeroDim
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 0))}
    {E : Set (EuclideanSpace ℝ (Fin 0))}
    (h_boundary : HasC2BoundaryIn Ω E) :
    frontier E = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hgrad : gradient h_boundary.boundary.definingFunction x = 0 := by
    -- The zero-dimensional ambient space is subsingleton, so every vector is `0`.
    exact Subsingleton.elim _ _
  have hfderiv : fderiv ℝ h_boundary.boundary.definingFunction x = 0 := by
    -- Transport the zero-gradient statement back to the Fréchet derivative.
    rw [← toDual_gradient (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin 0))
      (f := h_boundary.boundary.definingFunction) (x := x), hgrad]
    simp
  exact (h_boundary.boundary.regular_on_frontier x hx) hfderiv

/-- Helper for Example 8.12: the signed outward normal on `frontier E` extends
continuously to the closed unit ball of the ambient Euclidean space. -/
theorem continuousNormalExtension
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (f₀ : ℝ) :
    ∃ g : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d)),
      (∀ x, ‖g x‖ ≤ 1) ∧
      ∀ x ∈ frontier E, g x = Real.sign f₀ • h_boundary.outwardNormal x := by
  let nFront :
      C(frontier E, EuclideanSpace ℝ (Fin d)) :=
    ⟨fun x ↦ Real.sign f₀ • h_boundary.outwardNormal x, by
      -- Restrict the boundary `C¹` normal field to a continuous map on `frontier E`.
      exact continuousOn_iff_continuous_restrict.mp
        (h_boundary.isOutwardNormal.contDiffOn_normal.continuousOn.const_smul (Real.sign f₀))⟩
  have hFront_mem :
      ∀ x : frontier E, nFront x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    intro x
    -- The outward normal has unit norm on `frontier E`, and `|sign f₀| ≤ 1`.
    have hnorm : ‖nFront x‖ ≤ 1 := by
      change ‖Real.sign f₀ • h_boundary.outwardNormal x‖ ≤ 1
      rw [norm_smul, h_boundary.isOutwardNormal.norm_eq_one x x.2, mul_one]
      rcases lt_trichotomy f₀ 0 with hf₀ | rfl | hf₀
      · simp [Real.sign_of_neg hf₀]
      · simp
      · simp [Real.sign_of_pos hf₀]
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  obtain ⟨g, hg_mem, hg_restrict⟩ :=
    ContinuousMap.exists_forall_mem_restrict_eq isClosed_frontier nFront hFront_mem
  refine ⟨g, ?_, ?_⟩
  · intro x
    simpa [Metric.mem_closedBall, dist_zero_right] using hg_mem x
  · intro x hx
    have hrestrict :=
      congrArg
        (fun f : C(frontier E, EuclideanSpace ℝ (Fin d)) => f ⟨x, hx⟩)
        hg_restrict
    simpa [nFront] using hrestrict

/-- Helper for Example 8.12: a `C¹` compactly supported ambient field whose
topological support lies in `Ω` packages as an admissible test field once it
satisfies the pointwise norm bound. -/
lemma contDiffFieldToAdmissibleTestField
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hψ_cont : ContDiff ℝ 1 ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hψ_subset : tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hψ_norm : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))), ‖ψ x‖ ≤ 1) :
    ∃ v : AdmissibleTestField Ω, ∀ x, v.toTestFunction x = ψ x := by
  -- Package the ambient `C¹` field into the Chapter 8 admissible owner.
  refine ⟨AdmissibleTestField.ofTestFunction
      (TestFunction.mk ψ hψ_cont hψ_compact hψ_subset) ?_, ?_⟩
  · intro x hx
    simpa using hψ_norm x hx
  · intro x
    rfl

/-- Helper for Example 8.12: a compact piece of `frontier E` has an ambient open
neighborhood whose closure stays in `Ω` and on which the defining-function
gradient never vanishes. -/
lemma existsFrontierNeighborhoodGradientNeZeroOnCompact
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E) :
    ∃ U : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen U ∧
      K ⊆ U ∧
      closure U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      ∀ x ∈ U, gradient h_boundary.boundary.definingFunction x ≠ 0 := by
  let f := h_boundary.boundary.definingFunction
  let U₀ : Set (EuclideanSpace ℝ (Fin d)) :=
    (Ω : Set (EuclideanSpace ℝ (Fin d))) ∩
      {x | fderiv ℝ f x ≠ 0}
  have hU₀_open : IsOpen U₀ := by
    -- The `C²` defining function has continuous derivative on the open ambient domain `Ω`.
    refine
      (h_boundary.boundary.contDiffOn_definingFunction.continuousOn_fderiv_of_isOpen
        Ω.2 (by norm_num)).isOpen_inter_preimage Ω.2
        (isClosed_singleton : IsClosed
          ({0} : Set ((EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ))).isOpen_compl
  have hK_subset_U₀ : K ⊆ U₀ := by
    intro x hx
    refine ⟨h_boundary.frontier_subset (hK_subset hx), ?_⟩
    exact h_boundary.boundary.regular_on_frontier x (hK_subset hx)
  obtain ⟨U, hU_open, hKU, hUclosure⟩ :=
    normal_exists_closure_subset hK_compact.isClosed hU₀_open hK_subset_U₀
  refine ⟨U, hU_open, hKU, ?_, ?_⟩
  · -- The refined neighborhood still has compact closure inside `Ω`.
    exact fun x hx ↦ (hUclosure hx).1
  · intro x hxU
    have hxU₀ : x ∈ U₀ := hUclosure (subset_closure hxU)
    -- Route correction: use the `fderiv`-nonvanishing open neighborhood first, then
    -- transport it to a nonvanishing gradient via `toDual_gradient`.
    intro hgrad_zero
    have hfderiv_zero : fderiv ℝ f x = 0 := by
      rw [← toDual_gradient (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin d)) (f := f) (x := x), hgrad_zero]
      simp
    exact hxU₀.2 hfderiv_zero

/-- Helper for Example 8.12: on an open subset of `Ω`, the defining-function
gradient is `C¹`. -/
lemma contDiffOn_gradient
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU_open : IsOpen U)
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    ContDiffOn ℝ 1 (gradient h_boundary.boundary.definingFunction) U := by
  let f := h_boundary.boundary.definingFunction
  have hfderiv : ContDiffOn ℝ 1 (fderiv ℝ f) U := by
    -- Restrict the ambient `C²` regularity to the open patch `U` and differentiate once.
    simpa [f] using
      (h_boundary.boundary.contDiffOn_definingFunction.mono hU_subset).fderiv_of_isOpen
        (m := 1) hU_open (by norm_num)
  have hgrad' :
      ContDiffOn ℝ 1
        (fun x : EuclideanSpace ℝ (Fin d) =>
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ f x))
        U := by
    -- The gradient is the inverse Riesz transform applied to the Fréchet derivative.
    exact
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.contDiff.comp_contDiffOn
        hfderiv
  have hEq :
      (fun x : EuclideanSpace ℝ (Fin d) =>
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ f x)) =
      gradient f := by
    funext x
    apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).injective
    simp [f]
  simpa [hEq] using hgrad'

/-- Helper for Example 8.12: a compact frontier piece can be covered by the
finitely many coordinate patches on which one fixed gradient component is
nonzero. -/
lemma existsFiniteCoordinateGradientCoverOnCompact
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E) :
    ∃ V : Fin d → Set (EuclideanSpace ℝ (Fin d)),
      (∀ i, IsOpen (V i)) ∧
      (∀ i, V i ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) ∧
      K ⊆ ⋃ i, V i ∧
      ∀ i x, x ∈ V i →
        gradient h_boundary.boundary.definingFunction x i ≠ 0 := by
  obtain ⟨U, hU_open, hKU, hUclosure, hU_grad⟩ :=
    h_boundary.existsFrontierNeighborhoodGradientNeZeroOnCompact hK_compact hK_subset
  have hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
    -- The refined neighborhood stays inside `Ω` because it is contained in its closure.
    exact subset_closure.trans hUclosure
  have hgrad_cont :
      ContinuousOn (gradient h_boundary.boundary.definingFunction) U := by
    -- We only need continuity of the gradient to make the coordinate-nonzero patches open.
    exact (h_boundary.contDiffOn_gradient hU_open hU_subset).continuousOn
  let V : Fin d → Set (EuclideanSpace ℝ (Fin d)) := fun i =>
    U ∩ (fun x : EuclideanSpace ℝ (Fin d) =>
      gradient h_boundary.boundary.definingFunction x i) ⁻¹' ({0} : Set ℝ)ᶜ
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · intro i
    have hcoord_cont :
        ContinuousOn
          (fun x : EuclideanSpace ℝ (Fin d) =>
            gradient h_boundary.boundary.definingFunction x i)
          U := by
      exact
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).comp_continuousOn hgrad_cont
    -- Each coordinate-nonzero patch is open inside the regular neighborhood `U`.
    simpa [V] using
      hcoord_cont.isOpen_inter_preimage hU_open
        (isClosed_singleton : IsClosed ({0} : Set ℝ)).isOpen_compl
  · intro i x hx
    exact hU_subset hx.1
  · intro x hxK
    have hxU : x ∈ U := hKU hxK
    have hxCoord :
        ∃ i : Fin d, gradient h_boundary.boundary.definingFunction x i ≠ 0 := by
      by_contra hCoord
      apply hU_grad x hxU
      ext i
      have hi : ¬ gradient h_boundary.boundary.definingFunction x i ≠ 0 := by
        exact fun hi ↦ hCoord ⟨i, hi⟩
      simpa using hi
    rcases hxCoord with ⟨i, hi⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    exact ⟨hxU, hi⟩
  · intro i x hx
    exact hx.2

/-- Helper for Example 8.12: fixed-coordinate product coordinates insert back
into the ambient Euclidean space by a continuous linear map. -/
def insertCoordinateMap
    {n : ℕ}
    (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) := by
  let f : EuclideanSpace ℝ (Fin n) × ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    { toFun := fun p ↦
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
          (@Fin.insertNth (n := n) (α := fun _ : Fin (n + 1) => ℝ) i p.2
            ((EuclideanSpace.equiv (Fin n) ℝ) p.1))
      map_add' := by
        -- The coordinate insertion is pointwise additive in the product variables.
        intro p q
        apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
        ext j
        simp
      map_smul' := by
        -- Scalar multiplication is also coordinatewise after passing to the function model.
        intro c p
        apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
        ext j
        by_cases hj : j = i
        · subst hj
          simp
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
          simp }
  exact ⟨f, f.continuous_of_finiteDimensional⟩

/-- Helper for Example 8.12: deleting one distinguished coordinate is the
continuous linear inverse to `insertCoordinateMap`. -/
def removeCoordinateMap
    {n : ℕ}
    (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ := by
  let f : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
    { toFun := fun x ↦
        ( (EuclideanSpace.equiv (Fin n) ℝ).symm
            (fun j ↦ x (i.succAbove j)),
          x i )
      map_add' := by
        -- Removing the distinguished coordinate is coordinatewise additive.
        intro x y
        ext
        · simp
        · simp
      map_smul' := by
        -- Scalar multiplication is preserved in every remaining coordinate.
        intro c x
        ext
        · simp
        · simp }
  exact ⟨f, f.continuous_of_finiteDimensional⟩

/-- Helper for Example 8.12: the fixed-coordinate insertion map is smooth, so
it can be fed to the implicit-function theorem without reopening the transport
to plain coordinate tuples. -/
lemma contDiff_insertCoordinateMap
    {n : ℕ}
    (i : Fin (n + 1)) :
    ContDiff ℝ 2 (insertCoordinateMap i) := by
  -- Route correction: package the `insertNth` transport once as a continuous linear map,
  -- then smoothness is immediate from the bundled linear API.
  simpa [insertCoordinateMap] using (insertCoordinateMap i).contDiff

/-- Helper for Example 8.12: the inserted coordinate really is the distinguished
scalar coordinate in the ambient space. -/
lemma insertCoordinateMap_apply_self
    {n : ℕ}
    (i : Fin (n + 1))
    (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    (insertCoordinateMap i p).ofLp i = p.2 := by
  -- Evaluate the bundled coordinate insertion at the distinguished slot.
  simp [insertCoordinateMap]

/-- Helper for Example 8.12: away from the distinguished coordinate, the
insertion map recovers the original base coordinates. -/
lemma insertCoordinateMap_apply_succAbove
    {n : ℕ}
    (i : Fin (n + 1))
    (p : EuclideanSpace ℝ (Fin n) × ℝ)
    (j : Fin n) :
    (insertCoordinateMap i p).ofLp (i.succAbove j) = p.1.ofLp j := by
  -- The remaining coordinates are untouched by the insertion.
  simp [insertCoordinateMap]

/-- Helper for Example 8.12: removing the distinguished coordinate recovers the
ambient coordinates away from that slot. -/
lemma removeCoordinateMap_apply_succAbove
    {n : ℕ}
    (i : Fin (n + 1))
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (j : Fin n) :
    (removeCoordinateMap i x).1.ofLp j = x (i.succAbove j) := by
  -- Evaluate the deleted-coordinate map in the surviving base direction.
  simp [removeCoordinateMap]

/-- Helper for Example 8.12: removing the distinguished coordinate remembers
that scalar coordinate in the second product component. -/
lemma removeCoordinateMap_apply_self
    {n : ℕ}
    (i : Fin (n + 1))
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    (removeCoordinateMap i x).2 = x i := by
  -- The second component is exactly the deleted coordinate.
  rfl

/-- Helper for Example 8.12: deleting a coordinate after inserting it recovers
the original product point. -/
lemma removeCoordinateMap_insertCoordinateMap
    {n : ℕ}
    (i : Fin (n + 1))
    (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    removeCoordinateMap i (insertCoordinateMap i p) = p := by
  -- The two coordinate transports were designed to be inverse on the product side.
  ext
  · simp [removeCoordinateMap_apply_succAbove, insertCoordinateMap_apply_succAbove]
  · simp [removeCoordinateMap_apply_self, insertCoordinateMap_apply_self]

/-- Helper for Example 8.12: deleting the distinguished basis vector produces
the pure vertical product basis vector. -/
lemma removeCoordinateMap_single_self
    {n : ℕ}
    (i : Fin (n + 1))
    (t : ℝ) :
    removeCoordinateMap i (EuclideanSpace.single i t) =
      ((0 : EuclideanSpace ℝ (Fin n)), t) := by
  -- The deleted coordinate becomes the scalar component, and every surviving base coordinate
  -- vanishes on the distinguished ambient basis vector.
  ext
  · ext j
    simp [removeCoordinateMap_apply_succAbove, EuclideanSpace.single]
  · simp [removeCoordinateMap_apply_self, EuclideanSpace.single]

/-- Helper for Example 8.12: deleting a complementary ambient basis vector
produces the matching pure base product basis vector. -/
lemma removeCoordinateMap_single_succAbove
    {n : ℕ}
    (i : Fin (n + 1))
    (j : Fin n)
    (t : ℝ) :
    removeCoordinateMap i (EuclideanSpace.single (i.succAbove j) t) =
      ((EuclideanSpace.single j t : EuclideanSpace ℝ (Fin n)), 0) := by
  -- The complementary ambient basis vector survives entirely in the base coordinates while the
  -- deleted scalar slot is zero.
  ext
  · ext k
    by_cases hk : k = j
    · subst hk
      simp [removeCoordinateMap_apply_succAbove, EuclideanSpace.single]
    · simp [removeCoordinateMap_apply_succAbove, EuclideanSpace.single, hk]
  · simp [removeCoordinateMap_apply_self, EuclideanSpace.single]

/-- Helper for Example 8.12: inserting the removed coordinate data reconstructs
the original ambient point. -/
lemma insertCoordinateMap_removeCoordinateMap
    {n : ℕ}
    (i : Fin (n + 1))
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    insertCoordinateMap i (removeCoordinateMap i x) = x := by
  -- Check the distinguished coordinate and the complementary coordinates separately.
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
  ext j
  by_cases hj : j = i
  · subst hj
    simp [removeCoordinateMap_apply_self, insertCoordinateMap_apply_self]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [removeCoordinateMap_apply_succAbove, insertCoordinateMap_apply_succAbove]

/-- Helper for Example 8.12: `insertCoordinateMap` is a continuous linear
equivalence, so later local chart arguments may move freely between ambient and
product coordinates. -/
lemma insertCoordinateMap_isInvertible
    {n : ℕ}
    (i : Fin (n + 1)) :
    (insertCoordinateMap i).IsInvertible := by
  -- Route correction: package the inverse coordinate transport once here so the
  -- implicit-function patch proof does not rebuild it locally.
  refine ⟨ContinuousLinearEquiv.ofBijective (insertCoordinateMap i) ?_ ?_, rfl⟩
  · refine LinearMap.ker_eq_bot.mpr ?_
    intro p q hpq
    have h := congrArg (removeCoordinateMap i) hpq
    simpa [removeCoordinateMap_insertCoordinateMap] using h
  · refine LinearMap.range_eq_top.mpr ?_
    intro x
    refine ⟨removeCoordinateMap i x, ?_⟩
    simp [insertCoordinateMap_removeCoordinateMap]

/-- Helper for Example 8.12: inserting one split coordinate preserves ambient
volume after passing through the standard coordinate measurable equivalences. -/
lemma insertCoordinateMap_measurePreserving
    {n : ℕ}
    (i : Fin (n + 1)) :
    MeasureTheory.MeasurePreserving
      (insertCoordinateMap i)
      (MeasureTheory.volume)
      (MeasureTheory.volume) := by
  let eBase : EuclideanSpace ℝ (Fin n) ≃ᵐ (Fin n → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
  let eAmb : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm
  let eProd : EuclideanSpace ℝ (Fin n) × ℝ ≃ᵐ ((Fin n → ℝ) × ℝ) :=
    MeasurableEquiv.prodCongr eBase (MeasurableEquiv.refl ℝ)
  let eSwap : ((Fin n → ℝ) × ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
    MeasurableEquiv.prodComm
  let eInsert : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  let e : EuclideanSpace ℝ (Fin n) × ℝ ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
    eProd.trans <| eSwap.trans <| eInsert.trans eAmb.symm
  have heq :
      (e : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin (n + 1))) =
        insertCoordinateMap i := by
    funext p
    -- Compare the inserted coordinates after transporting both sides to plain functions.
    apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
    ext j
    by_cases hj : j = i
    · subst hj
      calc
        (e p).ofLp j = (eSwap (eProd p)).1 := by
          simp [e, eInsert, eAmb, MeasurableEquiv.piFinSuccAbove_symm_apply, PiLp.toLp_apply]
        _ = p.2 := by
          rfl
        _ = ((insertCoordinateMap j) p).ofLp j := by
          simpa using (insertCoordinateMap_apply_self j p).symm
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      calc
        (e p).ofLp (i.succAbove k) = (eSwap (eProd p)).2 k := by
          simp [e, eInsert, eAmb, MeasurableEquiv.piFinSuccAbove_symm_apply, PiLp.toLp_apply]
        _ = p.1.ofLp k := by
          rfl
        _ = ((insertCoordinateMap i) p).ofLp (i.succAbove k) := by
          simpa using (insertCoordinateMap_apply_succAbove i p k).symm
  have hBase :
      MeasureTheory.MeasurePreserving eBase MeasureTheory.volume MeasureTheory.volume := by
    -- The standard Euclidean coordinates are an isometric measurable equivalence.
    simpa [eBase] using
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n))
  have hAmb :
      MeasureTheory.MeasurePreserving eAmb MeasureTheory.volume MeasureTheory.volume := by
    -- The ambient Euclidean coordinates are handled the same way.
    simpa [eAmb] using
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1)))
  have hProd :
      MeasureTheory.MeasurePreserving eProd MeasureTheory.volume MeasureTheory.volume := by
    -- Product coordinates preserve volume because each factor does.
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.volume_eq_prod]
    simpa [eProd, MeasurableEquiv.prodCongr] using
      hBase.prod (MeasureTheory.MeasurePreserving.id MeasureTheory.volume)
  have hSwap :
      MeasureTheory.MeasurePreserving eSwap MeasureTheory.volume MeasureTheory.volume := by
    -- Swapping the two product coordinates does not change product volume.
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.volume_eq_prod]
    simpa [eSwap, MeasurableEquiv.prodComm] using (MeasureTheory.Measure.measurePreserving_swap :
      MeasureTheory.MeasurePreserving Prod.swap
        (MeasureTheory.volume.prod MeasureTheory.volume)
        (MeasureTheory.volume.prod MeasureTheory.volume))
  have hInsert :
      MeasureTheory.MeasurePreserving eInsert MeasureTheory.volume MeasureTheory.volume := by
    -- Inserting the distinguished scalar coordinate is the standard `Fin.succAbove` permutation.
    simpa [eInsert] using
      (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hcomp :
      MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume := by
    -- Compose the four canonical coordinate transports.
    convert hAmb.symm.comp (hInsert.comp (hSwap.comp hProd)) using 1
    ext p
    rfl
  simpa [heq] using hcomp

/-- Helper for Example 8.12: the fixed-coordinate insertion map is globally
Lipschitz, so later graph-image arguments can transport product-coordinate
patches to the ambient Euclidean space with one stable measure bound. -/
lemma insertCoordinateMap_lipschitz
    {n : ℕ}
    (i : Fin (n + 1)) :
    LipschitzWith ‖insertCoordinateMap i‖₊ (insertCoordinateMap i) := by
  -- The operator norm of the bundled linear map gives the correct global Lipschitz control.
  exact (insertCoordinateMap i).lipschitz

/-- Helper for Example 8.12: on the frontier, the normalized defining-function
gradient recovers the packaged outward unit normal. -/
lemma normalizedGradient_eq_outwardNormal_onFrontier
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ frontier E) :
    ((‖gradient h_boundary.boundary.definingFunction x‖)⁻¹ : ℝ) •
        gradient h_boundary.boundary.definingFunction x =
      h_boundary.outwardNormal x := by
  -- Rewrite the gradient as a positive scalar multiple of the unit normal and normalize it.
  rcases h_boundary.isOutwardNormal.gradient_eq_pos_smul x hx with ⟨c, hc_pos, hgrad⟩
  rw [hgrad, norm_smul, Real.norm_eq_abs, h_boundary.isOutwardNormal.norm_eq_one x hx, mul_one,
    abs_of_pos hc_pos, smul_smul, inv_mul_cancel₀ hc_pos.ne', one_smul]

end HasC2BoundaryIn

/-- Helper for Example 8.12: a compact subset of an open ambient set admits a
`C¹` compactly supported cutoff that equals `1` on that compact subset and
stays between `0` and `1`. -/
lemma existsContDiffCompactSupportCutoffEqOneOnCompact
    {d : ℕ}
    {U K : Set (EuclideanSpace ℝ (Fin d))}
    (hU_open : IsOpen U)
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ U) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ 1 χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧
      Set.EqOn χ 1 K ∧
      ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨L, hL_compact, hKL, hLU⟩ :=
    exists_compact_between hK_compact hU_open hK_subset
  obtain ⟨V, hV_open, hKV, hVclosure⟩ :=
    normal_exists_closure_subset hK_compact.isClosed isOpen_interior hKL
  obtain ⟨χ, hχ_smooth, hχ_range, hχ_support, hχ_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d)))
      hV_open hK_compact.isClosed hKV
  refine ⟨χ, hχ_smooth.contDiff, ?_, ?_, ?_, fun x ↦ hχ_range ⟨x, rfl⟩⟩
  · -- The support is trapped inside the compact closure of the refined neighborhood.
    have hclosure_compact : IsCompact (closure V) := by
      refine hL_compact.of_isClosed_subset isClosed_closure ?_
      exact hVclosure.trans interior_subset
    have htsupport_compact : IsCompact (tsupport χ) := by
      simpa [tsupport, hχ_support] using hclosure_compact
    exact HasCompactSupport.intro htsupport_compact fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  · -- The compactly supported cutoff still lives inside the original open set `U`.
    simpa [tsupport, hχ_support] using
      hVclosure.trans (interior_subset.trans hLU)
  · -- On the compact core, the cutoff takes the exact constant value `1`.
    intro x hx
    exact (hχ_one x).1 hx

/-- Helper for Example 8.12: a compact subset of `Ω` admits a continuous
compactly supported cutoff that equals `1` on that subset and stays between `0`
and `1`. -/
lemma existsCompactlySupportedCutoff_eqOneOnCompact
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ,
      Continuous χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      Set.EqOn χ 1 K ∧
      ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  -- Use Urysohn's lemma to localize later boundary test fields near compact subsets.
  obtain ⟨χ, hχ_one, hχ_tsupport_compact, hχ_subset, hχ_range⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK_compact Ω.2 hK_subset
  refine ⟨χ, χ.continuous, ?_, hχ_subset, hχ_one, hχ_range⟩
  exact HasCompactSupport.intro hχ_tsupport_compact fun x hx ↦ image_eq_zero_of_notMem_tsupport hx

/-- On the boundary, the inner product of an admissible field and a unit normal
has norm at most `1`. -/
lemma boundaryInner_norm_le_one
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_frontier_subset : frontier E ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (n : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hn_unit : ∀ x ∈ frontier E, ‖n x‖ = 1)
    (v : AdmissibleTestField Ω)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ frontier E) :
    ‖inner ℝ (v.toTestFunction x) (n x)‖ ≤ 1 := by
  have hv : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x (h_frontier_subset hx)
  have hn : ‖n x‖ ≤ 1 := by simp [hn_unit x hx]
  calc
    ‖inner ℝ (v.toTestFunction x) (n x)‖ ≤ ‖v.toTestFunction x‖ * ‖n x‖ :=
      norm_inner_le_norm _ _
    _ ≤ 1 * 1 := mul_le_mul hv hn (norm_nonneg _) (by positivity)
    _ = 1 := by ring

/-- If an admissible field agrees with `Real.sign f₀ • n` on `frontier E`, then
the boundary integrand is the constant `Real.sign f₀`. -/
lemma boundaryInner_eq_sign_of_normalExtension
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    {f₀ : ℝ}
    (n : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hn_unit : ∀ x ∈ frontier E, ‖n x‖ = 1)
    (v : AdmissibleTestField Ω)
    (h_normal_extension :
      ∀ x ∈ frontier E, v.toTestFunction x = Real.sign f₀ • n x)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ frontier E) :
    inner ℝ (v.toTestFunction x) (n x) = Real.sign f₀ := by
  rw [h_normal_extension x hx, real_inner_smul_left, real_inner_self_eq_norm_sq, hn_unit x hx]
  norm_num

/-- Multiplying a real number by its sign recovers its absolute value. -/
lemma mul_sign_eq_abs (a : ℝ) : a * Real.sign a = |a| := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [Real.sign_of_neg ha, abs_of_neg ha]
    ring
  · simp
  · rw [Real.sign_of_pos ha, abs_of_nonneg ha.le]
    ring

/-- Helper for Example 8.12: the normalized gradient has unit norm wherever the
gradient does not vanish. -/
lemma norm_normalizedGradient_eq_one
    {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : gradient f x ≠ 0) :
    ‖(((‖gradient f x‖)⁻¹ : ℝ) • gradient f x)‖ = 1 := by
  -- Expand the norm of the scalar multiple and use `‖gradient f x‖ ≠ 0`.
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- Helper for Example 8.12: on an open regular neighborhood, the normalized
defining-function gradient is `C¹`. -/
lemma contDiffOn_normalizedGradient
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU_open : IsOpen U)
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hU_grad : ∀ x ∈ U, gradient h_boundary.boundary.definingFunction x ≠ 0) :
    ContDiffOn ℝ 1
      (fun x =>
        ((‖gradient h_boundary.boundary.definingFunction x‖)⁻¹ : ℝ) •
          gradient h_boundary.boundary.definingFunction x)
      U := by
  let f := h_boundary.boundary.definingFunction
  have hfderiv : ContDiffOn ℝ 1 (fderiv ℝ f) U := by
    -- A `C²` defining function has a `C¹` Fréchet derivative on every open subdomain.
    simpa [f] using
      (h_boundary.boundary.contDiffOn_definingFunction.mono hU_subset).fderiv_of_isOpen
        (m := 1) hU_open (by norm_num)
  have hgrad : ContDiffOn ℝ 1 (gradient f) U := by
    -- The gradient is just the inverse Riesz map applied to the Fréchet derivative.
    have hgrad' :
        ContDiffOn ℝ 1
          (fun x : EuclideanSpace ℝ (Fin d) =>
            (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ f x))
          U := by
      exact
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.contDiff.comp_contDiffOn
          hfderiv
    have hEq :
        (fun x : EuclideanSpace ℝ (Fin d) =>
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ f x)) =
        gradient f := by
      funext x
      apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).injective
      simp [f]
    simpa [hEq]
      using hgrad'
  have hnorm :
      ContDiffOn ℝ 1 (fun x => ‖gradient f x‖) U := by
    -- The norm is smooth away from the zero gradient locus.
    exact ContDiffOn.norm ℝ hgrad fun x hx => hU_grad x hx
  have hinv :
      ContDiffOn ℝ 1 (fun x => ((‖gradient f x‖)⁻¹ : ℝ)) U := by
    -- Invert the norm only on the regular neighborhood where it never vanishes.
    exact hnorm.inv fun x hx => norm_ne_zero_iff.mpr (hU_grad x hx)
  -- Multiply the scalar reciprocal by the gradient to obtain the normalized field.
  exact hinv.smul hgrad

/-- Helper for Example 8.12: a compact frontier piece admits a `C¹` cutoff whose
support stays inside a neighborhood where the defining-function gradient never
vanishes. -/
lemma HasC2BoundaryIn.existsFrontierCutoffWithRegularSupport
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ,
      ∃ U : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen U ∧
      ContDiff ℝ 1 χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧
      U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      Set.EqOn χ 1 K ∧
      (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ x ∈ U, gradient h_boundary.boundary.definingFunction x ≠ 0 := by
  obtain ⟨U, hU_open, hKU, hUclosure, hU_grad⟩ :=
    h_boundary.existsFrontierNeighborhoodGradientNeZeroOnCompact hK_compact hK_subset
  obtain ⟨χ, hχ_cont, hχ_compact, hχ_subsetU, hχ_one, hχ_range⟩ :=
    existsContDiffCompactSupportCutoffEqOneOnCompact hU_open hK_compact hKU
  refine ⟨χ, U, hU_open, hχ_cont, hχ_compact, hχ_subsetU, ?_, hχ_one, hχ_range, hU_grad⟩
  exact subset_closure.trans hUclosure

/-- Helper for Example 8.12: a compact frontier piece admits a thicker compact
core inside the regular neighborhood on which the cutoff is identically `1`. -/
lemma HasC2BoundaryIn.existsThickFrontierCutoffWithRegularSupport
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ,
      ∃ U L : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen U ∧
      IsCompact L ∧
      K ⊆ interior L ∧
      ContDiff ℝ 1 χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧
      L ⊆ U ∧
      U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      Set.EqOn χ 1 L ∧
      (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ x ∈ U, gradient h_boundary.boundary.definingFunction x ≠ 0 := by
  obtain ⟨U, hU_open, hKU, hUclosure, hU_grad⟩ :=
    h_boundary.existsFrontierNeighborhoodGradientNeZeroOnCompact hK_compact hK_subset
  obtain ⟨L, hL_compact, hKL, hLU⟩ :=
    exists_compact_between hK_compact hU_open hKU
  obtain ⟨χ, hχ_cont, hχ_compact, hχ_subsetU, hχ_one, hχ_range⟩ :=
    existsContDiffCompactSupportCutoffEqOneOnCompact hU_open hL_compact hLU
  refine ⟨χ, U, L, hU_open, hL_compact, hKL, hχ_cont, hχ_compact, hχ_subsetU, hLU, ?_,
    hχ_one, hχ_range, hU_grad⟩
  -- The regular neighborhood still sits inside the ambient open set `Ω`.
  exact subset_closure.trans hUclosure

/-- Helper for Example 8.12: if the support of a field avoids `frontier E`,
then the closure of the part of its support lying in `E` already sits inside
`interior E`. -/
lemma HasC2BoundaryIn.closureInterTsupportSubsetInteriorOfFrontierDisjoint
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (_h_boundary : HasC2BoundaryIn Ω E)
    {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hφ_frontier_disjoint : tsupport φ ∩ frontier E = ∅) :
    closure (E ∩ tsupport φ) ⊆ interior E := by
  intro x hx
  have hxClosureE : x ∈ closure E := closure_mono Set.inter_subset_left hx
  have hxSupport : x ∈ tsupport φ := by
    simpa only [IsClosed.closure_eq (isClosed_tsupport φ)] using
      (closure_mono Set.inter_subset_right hx)
  have hxNotFrontier : x ∉ frontier E := by
    have hnotMem : x ∉ tsupport φ ∩ frontier E := by
      simpa [hφ_frontier_disjoint]
    exact fun hxFrontier ↦ hnotMem ⟨hxSupport, hxFrontier⟩
  have hxInteriorOrFrontier : x ∈ interior E ∪ frontier E := by
    simpa [closure_eq_interior_union_frontier] using hxClosureE
  -- A closure point of `E` outside the frontier must already lie in the interior.
  exact hxInteriorOrFrontier.resolve_right hxNotFrontier

/-- Helper for Example 8.12: the image of a compact convex base set under a
fixed-coordinate `C¹` graph map has finite codimension-`0` Hausdorff
measure. -/
lemma graphImage_hausdorffMeasure_ne_top
    {n : ℕ}
    {i : Fin (n + 1)}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hC_convex : Convex ℝ C)
    (hC_compact : IsCompact C)
    (hψ_cont : ContDiffOn ℝ 1 ψ C) :
    (MeasureTheory.Measure.hausdorffMeasure (n : ℝ))
      ((fun z : EuclideanSpace ℝ (Fin n) ↦ HasC2BoundaryIn.insertCoordinateMap i (z, ψ z)) '' C) ≠ ⊤ := by
  let graphMap : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × ℝ := fun z ↦ (z, ψ z)
  obtain ⟨K, hψ_lipschitz⟩ :=
    hψ_cont.exists_lipschitzOnWith (by norm_num) hC_convex hC_compact
  have hgraph_lipschitz : LipschitzOnWith (max 1 K) graphMap C := by
    -- The product graph is Lipschitz because the identity and `ψ` are both Lipschitz on `C`.
    simpa [graphMap] using
      (LipschitzWith.id.lipschitzOnWith (s := C)).prodMk hψ_lipschitz
  have hbase_ne_top :
      (MeasureTheory.Measure.hausdorffMeasure (n : ℝ)) C ≠ ⊤ := by
    -- Compact subsets of Euclidean space have finite Hausdorff measure in the ambient dimension.
    exact hC_compact.measure_lt_top.ne
  have hgraphImage_ne_top :
      (MeasureTheory.Measure.hausdorffMeasure (n : ℝ)) (graphMap '' C) ≠ ⊤ := by
    have himage_le :=
      hgraph_lipschitz.hausdorffMeasure_image_le (d := (n : ℝ))
        (show 0 ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n)
    refine ne_of_lt <| lt_of_le_of_lt himage_le ?_
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (show 0 ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n) (by simp))
      hbase_ne_top.lt_top
  have himage_eq :
      HasC2BoundaryIn.insertCoordinateMap i '' (graphMap '' C) =
        ((fun z : EuclideanSpace ℝ (Fin n) ↦ HasC2BoundaryIn.insertCoordinateMap i (z, ψ z)) '' C) := by
    -- Reassociate the graph image so the bundled insertion map acts on the outside once.
    simpa [graphMap, Function.comp] using
      (Set.image_image (HasC2BoundaryIn.insertCoordinateMap i) graphMap C)
  set L := ‖HasC2BoundaryIn.insertCoordinateMap i‖₊
  have himage_le :=
    (HasC2BoundaryIn.insertCoordinateMap_lipschitz i).hausdorffMeasure_image_le
      (d := (n : ℝ))
      (show 0 ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n)
      (graphMap '' C)
  have himage_le' :
      (MeasureTheory.Measure.hausdorffMeasure (n : ℝ))
          ((fun z : EuclideanSpace ℝ (Fin n) ↦ HasC2BoundaryIn.insertCoordinateMap i (z, ψ z)) '' C) ≤
        ↑‖HasC2BoundaryIn.insertCoordinateMap i‖₊ ^ (n : ℝ) *
          (MeasureTheory.Measure.hausdorffMeasure (n : ℝ)) (graphMap '' C) := by
    simpa [himage_eq] using himage_le
  refine ne_of_lt <| lt_of_le_of_lt himage_le' ?_
  simpa [L] using
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg
        (show 0 ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n)
        (by simp))
      hgraphImage_ne_top.lt_top)

/-- Helper for Example 8.12: the image of a compact convex base set under a
fixed-coordinate `C¹` graph map has finite codimension-`0` Euclidean Hausdorff
measure. -/
lemma graphImage_surfaceMeasure_ne_top
    {n : ℕ}
    {i : Fin (n + 1)}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hC_convex : Convex ℝ C)
    (hC_compact : IsCompact C)
    (hψ_cont : ContDiffOn ℝ 1 ψ C) :
    (MeasureTheory.Measure.euclideanHausdorffMeasure n)
      ((fun z : EuclideanSpace ℝ (Fin n) ↦ HasC2BoundaryIn.insertCoordinateMap i (z, ψ z)) '' C) ≠ ⊤ := by
  have hhausdorff_ne_top :
      (MeasureTheory.Measure.hausdorffMeasure (n : ℝ))
        ((fun z : EuclideanSpace ℝ (Fin n) ↦ HasC2BoundaryIn.insertCoordinateMap i (z, ψ z)) '' C) ≠ ⊤ :=
    graphImage_hausdorffMeasure_ne_top hC_convex hC_compact hψ_cont
  -- Route correction: convert to Euclidean Hausdorff measure only after the raw Hausdorff bound.
  rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def, MeasureTheory.Measure.smul_apply]
  exact ENNReal.nnreal_smul_ne_top hhausdorff_ne_top

/-- Helper for Example 8.12: each coordinate summand in the raw divergence of
a `C¹` field is continuous. -/
lemma rawDivergenceSummandContinuous
    {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hφ_cont : ContDiff ℝ 1 φ)
    (i : Fin d) :
    Continuous
      (fun x ↦
        (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i) := by
  -- Route correction: keep the derivative evaluation in the `PiLp` normal form that Lean uses
  -- for Euclidean coordinates, then project to the `i`th scalar coordinate once.
  have hderiv :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          fderiv ℝ φ x (PiLp.single 2 i (1 : ℝ))) := by
    have happly :
        Continuous
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
            (fderiv ℝ φ p.1) p.2) :=
      hφ_cont.continuous_fderiv_apply (by norm_num)
    -- Freeze the basis direction before projecting to a scalar coordinate.
    have hfreeze :
        Continuous
          (fun x : EuclideanSpace ℝ (Fin d) ↦
            (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              (fderiv ℝ φ p.1) p.2)
              (x, WithLp.toLp 2 (Pi.single i (1 : ℝ)))) :=
      happly.comp (continuous_id.prodMk continuous_const)
    simpa [PiLp.toLp_single] using hfreeze
  have happly :
      Continuous (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i) :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i
  have hcoord :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i)
            (fderiv ℝ φ x (PiLp.single 2 i (1 : ℝ)))) :=
    happly.comp hderiv
  simpa using hcoord

/-- Helper for Example 8.12: each coordinate summand in the raw divergence of
a compactly supported `C¹` field has compact support. -/
lemma rawDivergenceSummandHasCompactSupport
    {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hφ_compact : HasCompactSupport φ)
    (i : Fin d) :
    HasCompactSupport
      (fun x ↦
        (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i) := by
  -- Route correction: use the same `PiLp` derivative spelling as the continuity lemma so the
  -- support projection is definitionally stable.
  have hderiv :
      HasCompactSupport
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          fderiv ℝ φ x (PiLp.single 2 i (1 : ℝ))) := by
    simpa using
      (hφ_compact.fderiv_apply ℝ (WithLp.toLp 2 (Pi.single i (1 : ℝ))))
  -- Push compact support through the coordinate projection.
  have hcoord :
      HasCompactSupport
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i)
            (fderiv ℝ φ x (PiLp.single 2 i (1 : ℝ)))) :=
    hderiv.comp_left (g := fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i) rfl
  simpa using hcoord

/-- Helper for Example 8.12: the raw divergence of a `C¹` field is continuous. -/
lemma rawDivergenceContinuous
    {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hφ_cont : ContDiff ℝ 1 φ) :
    Continuous
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ∑ i : Fin d, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i) := by
  -- Sum the coordinate continuity lemmas in the source-facing divergence spelling.
  exact continuous_finsetSum Finset.univ fun i _ ↦
    rawDivergenceSummandContinuous hφ_cont i

/-- Helper for Example 8.12: the raw divergence of a compactly supported `C¹`
field has compact support. -/
lemma rawDivergenceHasCompactSupport
    {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hφ_compact : HasCompactSupport φ) :
    HasCompactSupport
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ∑ i : Fin d, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i) := by
  let ψ : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun i x ↦
    (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i
  have hψ : ∀ i ∈ Finset.univ, HasCompactSupport (ψ i) := by
    intro i _
    simpa [ψ] using rawDivergenceSummandHasCompactSupport hφ_compact i
  have hsum :
      (∑ i : Fin d, ψ i) =
        fun x : EuclideanSpace ℝ (Fin d) ↦
          ∑ i : Fin d, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i := by
    funext x
    simp [ψ]
  -- Sum the coordinate support lemmas before returning to the raw divergence formula.
  rw [← hsum]
  exact HasCompactSupport.finset_sum (s := Finset.univ) hψ

/-- Helper for Example 8.12: the raw divergence of a compactly supported `C¹`
field is integrable against the Chapter 8 domain measure. -/
lemma rawDivergenceIntegrable
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hφ_cont : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ∑ i : Fin d, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i)
      (domainMeasure Ω) := by
  let divφ : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦
    ∑ i : Fin d, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i
  have hdiv_cont : Continuous divφ := by
    -- Continuity comes from the `C¹` regularity of the field.
    simpa [divφ] using rawDivergenceContinuous hφ_cont
  have hdiv_compact : HasCompactSupport divφ := by
    -- Compact support is inherited from the original field through the derivative.
    simpa [divφ] using rawDivergenceHasCompactSupport hφ_compact
  have hdiv_on :
      MeasureTheory.IntegrableOn divφ (tsupport divφ) (domainMeasure Ω) := by
    have htsupport_meas : MeasurableSet (tsupport divφ) := (isClosed_tsupport divφ).measurableSet
    have htsupport_ne_top : (domainMeasure Ω) (tsupport divφ) ≠ ⊤ := by
      rw [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
        MeasureTheory.Measure.restrict_apply htsupport_meas]
      exact MeasureTheory.measure_ne_top_of_subset Set.inter_subset_left <|
        (hdiv_compact.isCompact.measure_lt_top
          (μ := (MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))).ne
    -- A continuous function is integrable on its compact topological support once the restricted
    -- Euclidean measure is known to be finite there.
    exact
      hdiv_cont.continuousOn.integrableOn_of_subset_isCompact
        hdiv_compact.isCompact htsupport_meas subset_rfl htsupport_ne_top
  exact
    (MeasureTheory.integrableOn_iff_integrable_of_support_subset
      (subset_tsupport divφ)).mp hdiv_on

/-- Helper for Example 8.12: the raw divergence of a field vanishes away from the
topological support of that field. -/
lemma rawDivergence_eq_zero_of_notMem_tsupport
    {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ tsupport φ) :
    (∑ i : Fin d, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i) = 0 := by
  -- Each coordinate derivative vanishes once the field is locally zero.
  simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]

/-- Helper for Example 8.12: a compactly supported ambient `C¹` field on
Euclidean space has zero total raw divergence against volume. -/
lemma compactlySupported_divergence_eq_zero_volume
    {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hφ_cont : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ) :
    ∫ x,
        (∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(MeasureTheory.volume) = 0 := by
  let divφ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x ↦
    ∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i
  have hdiv_cont : Continuous divφ := by
    -- The raw divergence stays continuous because `φ` is `C¹`.
    simpa [divφ] using rawDivergenceContinuous hφ_cont
  have hdiv_support_subset : Function.support divφ ⊆ tsupport φ := by
    -- Outside the topological support of `φ`, every divergence summand vanishes.
    intro x hx
    by_contra hxφ
    exact hx <| by
      simpa [divφ] using rawDivergence_eq_zero_of_notMem_tsupport (φ := φ) hxφ
  have hdiv_tsupport_subset_tsupport : tsupport divφ ⊆ tsupport φ := by
    -- Passing from support to topological support is safe because `tsupport φ` is closed.
    simpa [tsupport] using closure_minimal hdiv_support_subset (isClosed_tsupport φ)
  obtain ⟨R₀, htsupport_ball₀⟩ :=
    hφ_compact.isCompact.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  let R : ℝ := max R₀ 1
  have hR_pos : 0 < R := by
    -- Enlarge the bounding radius to a strictly positive one so the comparison cube has interior.
    dsimp [R]
    positivity
  have htsupport_ball :
      tsupport φ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R := by
    -- The compact support sits in a slightly larger open ball.
    intro x hx
    exact Metric.ball_subset_ball (le_max_left _ _) (htsupport_ball₀ hx)
  let eL : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)
  -- Local instance justification (order transport): the box divergence theorem is stated for
  -- ordered ambient spaces, and the only natural order here is the coordinatewise order
  -- transported through `EuclideanSpace.equiv`.
  letI : Preorder (EuclideanSpace ℝ (Fin (n + 1))) := Preorder.lift eL
  let a : EuclideanSpace ℝ (Fin (n + 1)) :=
    show EuclideanSpace ℝ (Fin (n + 1)) from
      WithLp.toLp 2 (fun _ : Fin (n + 1) ↦ -R)
  let b : EuclideanSpace ℝ (Fin (n + 1)) :=
    show EuclideanSpace ℝ (Fin (n + 1)) from
      WithLp.toLp 2 (fun _ : Fin (n + 1) ↦ R)
  have hab : a ≤ b := by
    intro i
    change eL a i ≤ eL b i
    simp [eL, a, b, hR_pos.le]
  have hball_subset_box :
      Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R ⊆ Set.Icc a b := by
    -- A point of norm `< R` has every coordinate between `-R` and `R`.
    intro x hx
    constructor
    · intro i
      have hcoord :
          |x i| < R := by
        calc
          |x i| = ‖x i‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖x‖ := PiLp.norm_apply_le x i
          _ < R := by simpa [Metric.mem_ball, dist_zero_right] using hx
      have hcoord' := (abs_lt.mp hcoord).1
      change eL a i ≤ eL x i
      exact le_of_lt (by simpa [eL, a] using hcoord')
    · intro i
      have hcoord :
          |x i| < R := by
        calc
          |x i| = ‖x i‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖x‖ := PiLp.norm_apply_le x i
          _ < R := by simpa [Metric.mem_ball, dist_zero_right] using hx
      have hcoord' := (abs_lt.mp hcoord).2
      change eL x i ≤ eL b i
      exact le_of_lt (by simpa [eL, b] using hcoord')
  have hdiv_zero_outsideBox : ∀ x ∉ Set.Icc a b, divφ x = 0 := by
    -- The divergence vanishes outside the enclosing cube because `φ` itself does.
    intro x hxBox
    exact image_eq_zero_of_notMem_tsupport <| fun hxdiv ↦
      hxBox (hball_subset_box (htsupport_ball (hdiv_tsupport_subset_tsupport hxdiv)))
  let coord : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun i x ↦ φ x i
  let coordDeriv :
      Fin (n + 1) →
        EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
    fun i x ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ φ x)
  have hIcc_compact : IsCompact (Set.Icc a b) := by
    have hpre : Set.Icc a b = eL ⁻¹' Set.Icc (eL a) (eL b) := by
      ext x
      change (a ≤ x ∧ x ≤ b) ↔ (eL a ≤ eL x ∧ eL x ≤ eL b)
      rfl
    rw [hpre]
    exact (eL.toHomeomorph.isCompact_preimage).2
      (isCompact_Icc : IsCompact (Set.Icc (eL a) (eL b)))
  have hbox_integral :
      ∫ x in Set.Icc a b, divφ x ∂(MeasureTheory.volume) = 0 := by
    have hcube :
        ∫ x in Set.Icc a b, divφ x ∂(MeasureTheory.volume) =
          ∑ i : Fin (n + 1),
            ((∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
                coord i (eL.symm <| i.insertNth (eL b i) x) ∂MeasureTheory.volume) -
              ∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
                coord i (eL.symm <| i.insertNth (eL a i) x) ∂MeasureTheory.volume) := by
      -- Transport the field to coordinate space and apply the box divergence theorem there.
      refine MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_of_equiv
        eL (fun _ _ ↦ by rfl)
        (by
          change MeasureTheory.MeasurePreserving
            (@WithLp.ofLp 2 (Fin (n + 1) → ℝ))
          exact PiLp.volume_preserving_ofLp (Fin (n + 1)))
        coord coordDeriv ∅ (by simpa) a b hab ?_ ?_ divφ ?_ ?_
      · intro i
        exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hφ_cont.continuous).continuousOn
      · intro x _ i
        -- Differentiate the `i`th coordinate by composing with the continuous linear projection.
        exact ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
          ((hφ_cont.differentiable_one x).hasFDerivAt))
      · intro x
        -- This identifies the theorem's packaged divergence with the source-facing raw divergence.
        simp [divφ, coordDeriv, eL, EuclideanSpace.coe_proj, PiLp.toLp_single]
      · -- Continuity on the compact cube gives integrability of the divergence there.
        exact hdiv_cont.continuousOn.integrableOn_compact hIcc_compact
    have hfront_zero :
        ∀ i : Fin (n + 1),
          ∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            coord i (eL.symm <| i.insertNth (eL b i) x) ∂MeasureTheory.volume = 0 := by
      intro i
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero ?_
      intro x hx
      have hy_norm :
          R ≤ ‖eL.symm <| i.insertNth (eL b i) x‖ := by
        calc
          R = ‖(eL.symm <| i.insertNth (eL b i) x) i‖ := by
            rw [Real.norm_eq_abs]
            simpa [abs_of_nonneg hR_pos.le, eL, b]
          _ ≤ ‖eL.symm <| i.insertNth (eL b i) x‖ := PiLp.norm_apply_le _ i
      have hy_not_mem : eL.symm (i.insertNth (eL b i) x) ∉ tsupport φ := by
        intro hy_mem
        have hy_ball : eL.symm (i.insertNth (eL b i) x) ∈
            Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R :=
          htsupport_ball hy_mem
        exact (not_lt_of_ge hy_norm) <| by
          simpa [Metric.mem_ball, dist_zero_right] using hy_ball
      -- The field vanishes on every front face because the whole support lies strictly inside the cube.
      simpa [coord] using
        congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i)
          (image_eq_zero_of_notMem_tsupport hy_not_mem)
    have hback_zero :
        ∀ i : Fin (n + 1),
          ∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            coord i (eL.symm <| i.insertNth (eL a i) x) ∂MeasureTheory.volume = 0 := by
      intro i
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero ?_
      intro x hx
      have hy_norm :
          R ≤ ‖eL.symm <| i.insertNth (eL a i) x‖ := by
        calc
          R = ‖(eL.symm <| i.insertNth (eL a i) x) i‖ := by
            rw [Real.norm_eq_abs]
            simpa [abs_of_nonneg hR_pos.le, eL, a]
          _ ≤ ‖eL.symm <| i.insertNth (eL a i) x‖ := PiLp.norm_apply_le _ i
      have hy_not_mem : eL.symm (i.insertNth (eL a i) x) ∉ tsupport φ := by
        intro hy_mem
        have hy_ball : eL.symm (i.insertNth (eL a i) x) ∈
            Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R :=
          htsupport_ball hy_mem
        exact (not_lt_of_ge hy_norm) <| by
          simpa [Metric.mem_ball, dist_zero_right] using hy_ball
      -- The same support argument kills every back-face contribution.
      simpa [coord] using
        congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i)
          (image_eq_zero_of_notMem_tsupport hy_not_mem)
    calc
      ∫ x in Set.Icc a b, divφ x ∂(MeasureTheory.volume)
        = ∑ i : Fin (n + 1),
            ((∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
                coord i (eL.symm <| i.insertNth (eL b i) x) ∂MeasureTheory.volume) -
              ∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
                coord i (eL.symm <| i.insertNth (eL a i) x) ∂MeasureTheory.volume) := hcube
      _ = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        simp [hfront_zero i, hback_zero i]
  -- Route correction: isolate the Euclidean transport once in this whole-space helper so later
  -- local chart lemmas can call it without rebuilding the box argument.
  calc
    ∫ x, divφ x ∂(MeasureTheory.volume) = ∫ x in Set.Icc a b, divφ x ∂(MeasureTheory.volume) := by
      symm
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hdiv_zero_outsideBox
    _ = 0 := hbox_integral

namespace HasC2BoundaryIn

/-- Helper for Example 8.12: if a compactly supported ambient `C¹` field lives
in an open set whose closure stays inside `interior E`, then its divergence
integral over `E` vanishes. -/
lemma compactlySupportedInInterior_divergence_eq_zero
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {W : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hW_open : IsOpen W)
    (hW_subset : W ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hW_closure : closure W ⊆ interior E)
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hφ_cont : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_subsetW : tsupport φ ⊆ W) :
    ∫ x in E,
        (∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(domainMeasure Ω) = 0 := by
  let divφ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x ↦
    ∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i
  have hdiv_cont : Continuous divφ := by
    -- The raw divergence stays continuous because `φ` is `C¹`.
    simpa [divφ] using rawDivergenceContinuous hφ_cont
  have hdiv_support_subset : Function.support divφ ⊆ tsupport φ := by
    -- Outside the topological support of `φ`, every divergence summand vanishes.
    intro x hx
    by_contra hxφ
    exact hx <| by
      simpa [divφ] using rawDivergence_eq_zero_of_notMem_tsupport (φ := φ) hxφ
  have hdiv_tsupport_subset_tsupport : tsupport divφ ⊆ tsupport φ := by
    -- Passing from support to topological support is safe because `tsupport φ` is closed.
    simpa [tsupport] using closure_minimal hdiv_support_subset (isClosed_tsupport φ)
  have hdiv_tsupport_subsetΩ : tsupport divφ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The divergence still lives inside the ambient open domain.
    exact hdiv_tsupport_subset_tsupport.trans (hφ_subsetW.trans hW_subset)
  have hdiv_tsupport_subsetInterior :
      tsupport divφ ⊆ interior E := by
    -- The closure hypothesis on `W` pushes the whole divergence support into `interior E`.
    exact hdiv_tsupport_subset_tsupport.trans <| hφ_subsetW.trans <| subset_closure.trans hW_closure
  have hdiv_zero_outsideE : ∀ x ∉ E, divφ x = 0 := by
    -- Once the support is contained in `interior E`, the integrand vanishes on `Eᶜ`.
    intro x hxE
    exact image_eq_zero_of_notMem_tsupport <| fun hxdiv ↦
      hxE (interior_subset (hdiv_tsupport_subsetInterior hxdiv))
  have hdiv_zero_outsideΩ :
      ∀ x ∉ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), divφ x = 0 := by
    -- The same support localization shows that restricting to `Ω` does not change the integral.
    intro x hxΩ
    exact image_eq_zero_of_notMem_tsupport <| fun hxdiv ↦ hxΩ (hdiv_tsupport_subsetΩ hxdiv)
  -- Route correction: keep the Euclidean-space transport boxed inside this helper,
  -- then reduce the localized statement to the new whole-space divergence-zero lemma.
  rw [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  calc
    ∫ x in E, divφ x ∂((MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin (n + 1)))).restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      =
        ∫ x, divφ x ∂((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (n + 1)))).restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
            exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hdiv_zero_outsideE
    _ =
        ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), divφ x ∂(MeasureTheory.volume) := by
            rfl
    _ = ∫ x, divφ x ∂(MeasureTheory.volume) := by
            exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hdiv_zero_outsideΩ
    _ = 0 := by
            simpa [divφ] using compactlySupported_divergence_eq_zero_volume φ hφ_cont hφ_compact

/-- Helper for Example 8.12: inserting a pure scalar direction recovers the
corresponding ambient basis vector. -/
lemma insertCoordinateMap_zero_eq_single
    {n : ℕ}
    (i : Fin (n + 1))
    (t : ℝ) :
    HasC2BoundaryIn.insertCoordinateMap i (0, t) =
      EuclideanSpace.single i t := by
  -- Check the distinguished coordinate and the complementary coordinates separately.
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
  ext j
  by_cases hj : j = i
  · subst hj
    simp [HasC2BoundaryIn.insertCoordinateMap_apply_self, EuclideanSpace.single]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [HasC2BoundaryIn.insertCoordinateMap_apply_succAbove, EuclideanSpace.single]

/-- Helper for Example 8.12: inserting a pure base-coordinate direction recovers the
corresponding ambient basis vector away from the distinguished coordinate. -/
lemma insertCoordinateMap_single_zero_eq_single_succAbove
    {n : ℕ}
    (i : Fin (n + 1))
    (j : Fin n)
    (t : ℝ) :
    HasC2BoundaryIn.insertCoordinateMap i
        ((EuclideanSpace.single j t : EuclideanSpace ℝ (Fin n)), 0) =
      EuclideanSpace.single (i.succAbove j) t := by
  -- Check the distinguished coordinate and the complementary coordinates separately.
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
  ext k
  by_cases hk : k = i.succAbove j
  · subst hk
    simp [HasC2BoundaryIn.insertCoordinateMap_apply_succAbove, EuclideanSpace.single]
  · by_cases hki : k = i
    · subst hki
      simp [HasC2BoundaryIn.insertCoordinateMap_apply_self, EuclideanSpace.single]
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hki
      have hj' : j' ≠ j := by
        intro hj
        apply hk
        simpa [hj]
      simp [HasC2BoundaryIn.insertCoordinateMap_apply_succAbove, EuclideanSpace.single, hj']

/-- Helper for Example 8.12: differentiating the defining function along the
inserted scalar direction reads off the distinguished gradient coordinate. -/
lemma fderiv_definingFunction_insertCoordinateMap_zero
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (t : ℝ) :
    fderiv ℝ h_boundary.boundary.definingFunction x
        (HasC2BoundaryIn.insertCoordinateMap i (0, t)) =
      gradient h_boundary.boundary.definingFunction x i * t := by
  -- Transport the inserted scalar direction to the ambient basis vector and then use linearity.
  rw [insertCoordinateMap_zero_eq_single i t]
  have hsingle_smul :
      EuclideanSpace.single i t = t • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [EuclideanSpace.single]
    · simp [EuclideanSpace.single, hj]
  rw [hsingle_smul, map_smul]
  have hcoord :
      fderiv ℝ h_boundary.boundary.definingFunction x
          (EuclideanSpace.single i (1 : ℝ)) =
        gradient h_boundary.boundary.definingFunction x i := by
    -- Evaluating the Fréchet derivative on the `i`th basis vector extracts the `i`th gradient coordinate.
    rw [← toDual_gradient
      (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin (n + 1)))
      (f := h_boundary.boundary.definingFunction) (x := x)]
    simpa using
      (EuclideanSpace.inner_single_right i (1 : ℝ)
        (gradient h_boundary.boundary.definingFunction x))
  calc
    t •
        fderiv ℝ h_boundary.boundary.definingFunction x
          (EuclideanSpace.single i (1 : ℝ))
      = t • gradient h_boundary.boundary.definingFunction x i := by
          rw [hcoord]
    _ = gradient h_boundary.boundary.definingFunction x i * t := by
          simp [smul_eq_mul, mul_comm]

/-- Helper for Example 8.12: differentiating the defining function along an inserted
base direction reads off the corresponding ambient gradient coordinate. -/
lemma fderiv_definingFunction_insertCoordinateMap_single_zero
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (j : Fin n)
    (t : ℝ) :
    fderiv ℝ h_boundary.boundary.definingFunction x
        (HasC2BoundaryIn.insertCoordinateMap i
          ((EuclideanSpace.single j t : EuclideanSpace ℝ (Fin n)), 0)) =
      gradient h_boundary.boundary.definingFunction x (i.succAbove j) * t := by
  -- Transport the inserted base direction to the ambient basis vector and then use linearity.
  rw [insertCoordinateMap_single_zero_eq_single_succAbove i j t]
  have hsingle_smul :
      EuclideanSpace.single (i.succAbove j) t =
        t • EuclideanSpace.single (i.succAbove j) (1 : ℝ) := by
    ext k
    by_cases hk : k = i.succAbove j
    · subst hk
      simp [EuclideanSpace.single]
    · simp [EuclideanSpace.single, hk]
  rw [hsingle_smul, map_smul]
  have hcoord :
      fderiv ℝ h_boundary.boundary.definingFunction x
          (EuclideanSpace.single (i.succAbove j) (1 : ℝ)) =
        gradient h_boundary.boundary.definingFunction x (i.succAbove j) := by
    -- Evaluating on the ambient basis vector extracts the matching gradient coordinate.
    rw [← toDual_gradient
      (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin (n + 1)))
      (f := h_boundary.boundary.definingFunction) (x := x)]
    simpa using
      (EuclideanSpace.inner_single_right (i.succAbove j) (1 : ℝ)
        (gradient h_boundary.boundary.definingFunction x))
  calc
    t •
        fderiv ℝ h_boundary.boundary.definingFunction x
          (EuclideanSpace.single (i.succAbove j) (1 : ℝ))
      = t • gradient h_boundary.boundary.definingFunction x (i.succAbove j) := by
          rw [hcoord]
    _ = gradient h_boundary.boundary.definingFunction x (i.succAbove j) * t := by
          simp [smul_eq_mul, mul_comm]

/-- Helper for Example 8.12: one fixed-coordinate regular frontier point admits
an ambient compact core whose frontier lies in a single `C¹` graph image over
the complementary coordinates. -/
lemma fixedCoordinateFrontierGraphCore
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_open : IsOpen U)
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hU_grad : ∀ x ∈ U, gradient h_boundary.boundary.definingFunction x i ≠ 0)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
    (hx₀ : x₀ ∈ frontier E ∩ U) :
    ∃ L : Set (EuclideanSpace ℝ (Fin (n + 1))),
      ∃ C : Set (EuclideanSpace ℝ (Fin n)),
      ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        IsCompact L ∧
        x₀ ∈ interior L ∧
        L ⊆ U ∧
        IsCompact C ∧
        Convex ℝ C ∧
        ContDiffOn ℝ 1 ψ C ∧
        frontier E ∩ L ⊆
          ((fun z : EuclideanSpace ℝ (Fin n) ↦
              HasC2BoundaryIn.insertCoordinateMap i (z, ψ z)) '' C) := by
  -- Route correction: the compact-measure theorem only needs local graph containment on a compact
  -- core, so the missing local step is smaller than the earlier slab/atlas route.
  let f := h_boundary.boundary.definingFunction
  let u₀ := HasC2BoundaryIn.removeCoordinateMap i x₀
  let F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ :=
    f ∘ HasC2BoundaryIn.insertCoordinateMap i
  have hx₀_front : x₀ ∈ frontier E := hx₀.1
  have hx₀Ω : x₀ ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := hU_subset hx₀.2
  have hx₀_zero : f x₀ = 0 := by
    -- Frontier points are exactly the zero set of the defining function.
    have hx₀_front' : x₀ ∈ frontier E := hx₀.1
    rw [h_boundary.boundary.frontier_eq_zeroSet] at hx₀_front'
    exact hx₀_front'.2
  have hu₀_insert : HasC2BoundaryIn.insertCoordinateMap i u₀ = x₀ := by
    -- The fixed-coordinate charts are inverse at the chosen frontier point.
    simpa [u₀] using HasC2BoundaryIn.insertCoordinateMap_removeCoordinateMap i x₀
  have hF_u₀_zero : F u₀ = 0 := by
    -- The pulled-back defining function also vanishes at the frontier base point.
    simpa [F, hu₀_insert] using hx₀_zero
  have hF_contDiffAt : ContDiffAt ℝ 2 F u₀ := by
    have hf_contDiffAt : ContDiffAt ℝ 2 f x₀ := by
      -- Restrict the ambient `C²` defining function to the frontier base point.
      exact h_boundary.boundary.contDiffOn_definingFunction.contDiffAt (Ω.2.mem_nhds hx₀Ω)
    have hf_insert_contDiffAt : ContDiffAt ℝ 2 f (HasC2BoundaryIn.insertCoordinateMap i u₀) := by
      simpa [hu₀_insert] using hf_contDiffAt
    -- Compose the defining function with the fixed-coordinate insertion chart.
    simpa [F, f] using
      hf_insert_contDiffAt.comp u₀ (HasC2BoundaryIn.contDiff_insertCoordinateMap i).contDiffAt
  have hF_fderiv_eq :
      fderiv ℝ F u₀ = fderiv ℝ f x₀ ∘L HasC2BoundaryIn.insertCoordinateMap i := by
    have hf_hasFDerivAt : HasFDerivAt f (fderiv ℝ f x₀) x₀ := by
      -- The defining function is differentiable at the frontier base point.
      exact ((h_boundary.boundary.contDiffOn_definingFunction.contDiffAt
        (Ω.2.mem_nhds hx₀Ω)).differentiableAt (by norm_num)).hasFDerivAt
    have hf_insert_hasFDerivAt :
        HasFDerivAt f (fderiv ℝ f x₀) (HasC2BoundaryIn.insertCoordinateMap i u₀) := by
      simpa [hu₀_insert] using hf_hasFDerivAt
    have hcomp :
        HasFDerivAt F (fderiv ℝ f x₀ ∘L HasC2BoundaryIn.insertCoordinateMap i) u₀ := by
      -- Chain the defining-function derivative with the linear chart insertion.
      simpa [F, f] using
        hf_insert_hasFDerivAt.comp u₀ (HasC2BoundaryIn.insertCoordinateMap i).hasFDerivAt
    exact hcomp.fderiv
  have hF_inr_eq :
      fderiv ℝ F u₀ ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ =
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (gradient f x₀ i) := by
    apply ContinuousLinearMap.ext
    intro t
    -- Evaluate the partial derivative in the scalar direction and rewrite it through the gradient.
    calc
      (fderiv ℝ F u₀ ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ) t
        = fderiv ℝ f x₀ (HasC2BoundaryIn.insertCoordinateMap i (0, t)) := by
            simp [hF_fderiv_eq]
      _ = gradient f x₀ i * t := by
            simpa [f] using
              HasC2BoundaryIn.fderiv_definingFunction_insertCoordinateMap_zero
                h_boundary i x₀ t
      _ =
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (gradient f x₀ i)) t := by
            simp [ContinuousLinearMap.smulRight_apply, mul_comm]
  have hgrad_ne : gradient f x₀ i ≠ 0 := hU_grad x₀ hx₀.2
  have hF_inr_invertible :
      (fderiv ℝ F u₀ ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ).IsInvertible := by
    let g : ℝ →L[ℝ] ℝ :=
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((gradient f x₀ i)⁻¹)
    have hsmul_invertible :
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (gradient f x₀ i)).IsInvertible := by
      refine ContinuousLinearMap.IsInvertible.of_inverse (g := g) ?_ ?_
      · ext t
        simp [g, ContinuousLinearMap.smulRight_apply, mul_assoc, hgrad_ne, mul_comm, mul_left_comm]
      · ext t
        simp [g, ContinuousLinearMap.smulRight_apply, mul_assoc, hgrad_ne, mul_comm, mul_left_comm]
    simpa [hF_inr_eq] using hsmul_invertible
  let ψ := hF_contDiffAt.implicitFunction (pn := by norm_num) hF_inr_invertible
  have hψ_self : ψ u₀.1 = u₀.2 := by
    -- The implicit function passes through the original frontier point.
    simpa [ψ, u₀] using
      hF_contDiffAt.implicitFunction_apply_self (pn := by norm_num) hF_inr_invertible
  have hψ_contDiffAt : ContDiffAt ℝ 1 ψ u₀.1 := by
    -- The implicit chart inherits `C¹` regularity from the defining equation.
    exact
      (hF_contDiffAt.contDiffAt_implicitFunction (pn := by norm_num) hF_inr_invertible).of_le
        (by norm_num)
  obtain ⟨Bψ, hBψ_nhds, hψ_contDiffOn⟩ :=
    hψ_contDiffAt.contDiffOn (m := 1) le_rfl (by simp)
  have hgraphEq_nhds :
      {p : EuclideanSpace ℝ (Fin n) × ℝ | F p = 0 ↔ ψ p.1 = p.2} ∈ nhds u₀ := by
    -- Near `u₀`, the zero set of `F` is exactly the graph of the implicit function.
    filter_upwards
        [hF_contDiffAt.eventually_apply_eq_iff_implicitFunction
          (pn := by norm_num) hF_inr_invertible] with p hp
    simpa [hF_u₀_zero]
      using hp
  have hpreimageU_nhds :
      HasC2BoundaryIn.insertCoordinateMap i ⁻¹' U ∈ nhds u₀ := by
    -- Keep the local graph patch inside the original regular neighborhood `U`.
    have hpreimageU_open :
        IsOpen (HasC2BoundaryIn.insertCoordinateMap i ⁻¹' U) := by
      exact hU_open.preimage (HasC2BoundaryIn.insertCoordinateMap i).continuous
    have hu₀_mem_preimageU : u₀ ∈ HasC2BoundaryIn.insertCoordinateMap i ⁻¹' U := by
      change HasC2BoundaryIn.insertCoordinateMap i u₀ ∈ U
      simpa [hu₀_insert] using hx₀.2
    exact hpreimageU_open.mem_nhds hu₀_mem_preimageU
  have hprod_nhds :
      ({p : EuclideanSpace ℝ (Fin n) × ℝ | F p = 0 ↔ ψ p.1 = p.2} ∩
        HasC2BoundaryIn.insertCoordinateMap i ⁻¹' U) ∈ nhds u₀ := by
    exact Filter.inter_mem hgraphEq_nhds hpreimageU_nhds
  obtain ⟨s, hs_nhds, t, ht_nhds, hst_subset⟩ :=
    mem_nhds_prod_iff.mp hprod_nhds
  have hst_graph :
      s ×ˢ t ⊆ {p : EuclideanSpace ℝ (Fin n) × ℝ | F p = 0 ↔ ψ p.1 = p.2} := by
    intro p hp
    exact (hst_subset hp).1
  have hst_preimageU :
      s ×ˢ t ⊆ HasC2BoundaryIn.insertCoordinateMap i ⁻¹' U := by
    intro p hp
    exact (hst_subset hp).2
  obtain ⟨r₁, hr₁_pos, hr₁_subset⟩ :=
    Metric.mem_nhds_iff.mp
      (show s ∩ Bψ ∈ nhds u₀.1 from Filter.inter_mem hs_nhds hBψ_nhds)
  obtain ⟨r₂, hr₂_pos, hr₂_subset⟩ := Metric.mem_nhds_iff.mp ht_nhds
  have hball_subset_s : Metric.ball u₀.1 r₁ ⊆ s := by
    intro z hz
    exact (hr₁_subset hz).1
  have hball_subset_Bψ : Metric.ball u₀.1 r₁ ⊆ Bψ := by
    intro z hz
    exact (hr₁_subset hz).2
  let C : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall u₀.1 (r₁ / 2)
  let T : Set ℝ := Metric.closedBall u₀.2 (r₂ / 2)
  let L : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    HasC2BoundaryIn.insertCoordinateMap i '' (C ×ˢ T)
  have hhalf_r₁ : r₁ / 2 < r₁ := by linarith
  have hhalf_r₂ : r₂ / 2 < r₂ := by linarith
  have hC_subset_s : C ⊆ s := by
    intro z hz
    exact hball_subset_s (Metric.closedBall_subset_ball hhalf_r₁ hz)
  have hC_subset_Bψ : C ⊆ Bψ := by
    intro z hz
    exact hball_subset_Bψ (Metric.closedBall_subset_ball hhalf_r₁ hz)
  have hT_subset_t : T ⊆ t := by
    intro τ hτ
    exact hr₂_subset (Metric.closedBall_subset_ball hhalf_r₂ hτ)
  have hCT_subset :
      C ×ˢ T ⊆ s ×ˢ t := Set.prod_mono hC_subset_s hT_subset_t
  have hL_compact : IsCompact L := by
    -- The ambient compact core is the image of a compact product box under a linear chart.
    exact (isCompact_closedBall u₀.1 (r₁ / 2)).prod (isCompact_closedBall u₀.2 (r₂ / 2))
      |>.image (HasC2BoundaryIn.insertCoordinateMap i).continuous
  have hu₀_mem_interiorC : u₀.1 ∈ interior C := by
    -- The base point lies in the interior of the compact base closed ball.
    have hr₁_half_pos : 0 < r₁ / 2 := by linarith
    rw [mem_interior_iff_mem_nhds]
    exact Metric.closedBall_mem_nhds u₀.1 hr₁_half_pos
  have hu₀_mem_interiorT : u₀.2 ∈ interior T := by
    -- The scalar coordinate also lies in the interior of its compact closed interval.
    have hr₂_half_pos : 0 < r₂ / 2 := by linarith
    rw [mem_interior_iff_mem_nhds]
    exact Metric.closedBall_mem_nhds u₀.2 hr₂_half_pos
  have hu₀_mem_interiorProd : u₀ ∈ interior (C ×ˢ T) := by
    -- Product interiors split coordinatewise for the compact box.
    rw [interior_prod_eq]
    exact ⟨hu₀_mem_interiorC, hu₀_mem_interiorT⟩
  obtain ⟨e, he⟩ := HasC2BoundaryIn.insertCoordinateMap_isInvertible i
  have he_fun :
      ∀ p : EuclideanSpace ℝ (Fin n) × ℝ,
        e p = HasC2BoundaryIn.insertCoordinateMap i p := by
    intro p
    simpa using congrArg
      (fun m : EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) => m p) he
  have hx₀_mem_openImage : x₀ ∈ e '' interior (C ×ˢ T) := by
    refine ⟨u₀, hu₀_mem_interiorProd, ?_⟩
    have he_u₀ : e u₀ = HasC2BoundaryIn.insertCoordinateMap i u₀ := by
      exact he_fun u₀
    rw [he_u₀]
    simpa [u₀] using HasC2BoundaryIn.insertCoordinateMap_removeCoordinateMap i x₀
  have hOpenImage_subset_L : e '' interior (C ×ˢ T) ⊆ L := by
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    have he_p : e p = HasC2BoundaryIn.insertCoordinateMap i p := by
      exact he_fun p
    exact ⟨p, interior_subset hp, he_p.symm⟩
  have hx₀_mem_interiorL : x₀ ∈ interior L := by
    -- Transport the interior product box through the linear equivalence to get interior in `L`.
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset ((e.isOpenMap _ isOpen_interior).mem_nhds hx₀_mem_openImage)
      hOpenImage_subset_L
  have hL_subsetU : L ⊆ U := by
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    exact hst_preimageU (hCT_subset hp)
  have hψ_contDiffOn_C : ContDiffOn ℝ 1 ψ C := hψ_contDiffOn.mono hC_subset_Bψ
  have hfrontier_graph :
      frontier E ∩ L ⊆
        ((fun z : EuclideanSpace ℝ (Fin n) ↦
            HasC2BoundaryIn.insertCoordinateMap i (z, ψ z)) '' C) := by
    intro y hy
    rcases hy.2 with ⟨p, hp, rfl⟩
    have hp_graph : p ∈ {q : EuclideanSpace ℝ (Fin n) × ℝ | F q = 0 ↔ ψ q.1 = q.2} := by
      exact hst_graph (hCT_subset hp)
    have hp_zero : F p = 0 := by
      -- Frontier points on the local core still satisfy the defining equation `f = 0`.
      have hfront' :
          HasC2BoundaryIn.insertCoordinateMap i p ∈
            {x | x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∧ f x = 0} := by
        simpa [h_boundary.boundary.frontier_eq_zeroSet] using hy.1
      simpa [F, f] using hfront'.2
    refine ⟨p.1, hp.1, ?_⟩
    -- Replace the scalar coordinate by the implicit graph value on the zero set.
    simp [hp_graph.mp hp_zero]
  refine ⟨L, C, ψ, hL_compact, hx₀_mem_interiorL, hL_subsetU, ?_, ?_, hψ_contDiffOn_C,
    hfrontier_graph⟩
  · simpa [C] using isCompact_closedBall u₀.1 (r₁ / 2)
  · simpa [C] using convex_closedBall u₀.1 (r₁ / 2)

/-- Helper for Example 8.12: at a point where a continuous scalar field is nonzero on
an open set, one can orient the field by a sign `σ ∈ {1, -1}` so that `σ * g`
stays strictly positive on a smaller open neighborhood. -/
lemma existsSignedNeighborhood_mul_pos
    {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU_open : IsOpen U)
    {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg_cont : ContinuousOn g U)
    {x₀ : EuclideanSpace ℝ (Fin d)}
    (hx₀ : x₀ ∈ U)
    (hgx₀ : g x₀ ≠ 0) :
    ∃ σ : ℝ,
      (σ = 1 ∨ σ = -1) ∧
      ∃ W : Set (EuclideanSpace ℝ (Fin d)),
        IsOpen W ∧
        x₀ ∈ W ∧
        W ⊆ U ∧
        ∀ x ∈ W, 0 < σ * g x := by
  let σ : ℝ := if 0 < g x₀ then 1 else -1
  have hσ_cases : σ = 1 ∨ σ = -1 := by
    by_cases hpos : 0 < g x₀
    · left
      simp [σ, hpos]
    · right
      simp [σ, hpos]
  have hσ_mul_x₀ : 0 < σ * g x₀ := by
    by_cases hpos : 0 < g x₀
    · rw [show σ = 1 by simp [σ, hpos]]
      simpa using hpos
    · have hneg : g x₀ < 0 := by
        rcases lt_or_gt_of_ne hgx₀ with hlt | hgt
        · exact hlt
        · exact False.elim (hpos hgt)
      rw [show σ = -1 by simp [σ, hpos]]
      nlinarith
  have hσg_contAt : ContinuousAt (fun x : EuclideanSpace ℝ (Fin d) ↦ σ * g x) x₀ := by
    exact
      (continuousAt_const.mul
        (hg_cont.continuousAt (hU_open.mem_nhds hx₀)))
  let W : Set (EuclideanSpace ℝ (Fin d)) := U ∩ {x | 0 < σ * g x}
  have hW_mem : W ∈ nhds x₀ := by
    have hpos_mem :
        {x : EuclideanSpace ℝ (Fin d) | 0 < σ * g x} ∈ nhds x₀ := by
      exact hσg_contAt.preimage_mem_nhds (Ioi_mem_nhds hσ_mul_x₀)
    exact Filter.inter_mem (hU_open.mem_nhds hx₀) hpos_mem
  obtain ⟨W', hW'_subset, hW'_open, hx₀W'⟩ := mem_nhds_iff.mp hW_mem
  refine ⟨σ, hσ_cases, W', hW'_open, hx₀W', ?_, ?_⟩
  · intro x hx
    exact (hW'_subset hx).1
  · intro x hx
    exact (hW'_subset hx).2

/-- Helper for Example 8.12: one fixed-coordinate regular frontier point admits a compact
graph core on which the distinguished gradient coordinate has a fixed positive sign after
choosing `σ ∈ {1, -1}`. -/
lemma fixedCoordinateSignedGraphCore
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_open : IsOpen U)
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hU_grad : ∀ x ∈ U, gradient h_boundary.boundary.definingFunction x i ≠ 0)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
    (hx₀ : x₀ ∈ frontier E ∩ U) :
    ∃ σ : ℝ,
      ∃ L : Set (EuclideanSpace ℝ (Fin (n + 1))),
      ∃ C : Set (EuclideanSpace ℝ (Fin n)),
      ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        (σ = 1 ∨ σ = -1) ∧
        IsCompact L ∧
        x₀ ∈ interior L ∧
        L ⊆ U ∧
        IsCompact C ∧
        Convex ℝ C ∧
        ContDiffOn ℝ 1 ψ C ∧
        frontier E ∩ L ⊆
          ((fun z : EuclideanSpace ℝ (Fin n) ↦
              HasC2BoundaryIn.insertCoordinateMap i (z, ψ z)) '' C) ∧
        ∀ x ∈ L, 0 < σ * gradient h_boundary.boundary.definingFunction x i := by
  obtain ⟨L₀, C, ψ, hL₀_compact, hx₀L₀, hL₀_subset, hC_compact, hC_convex, hψ_cont, hgraph⟩ :=
    fixedCoordinateFrontierGraphCore h_boundary i hU_open hU_subset hU_grad hx₀
  have hgrad_cont :
      ContinuousOn
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          gradient h_boundary.boundary.definingFunction x i)
        U := by
    -- The distinguished gradient coordinate is continuous on the regular patch `U`.
    exact
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 1) => ℝ) i).comp_continuousOn
        ((h_boundary.contDiffOn_gradient hU_open hU_subset).continuousOn)
  obtain ⟨σ, hσ_cases, W, hW_open, hx₀W, hW_subset, hW_pos⟩ :=
    existsSignedNeighborhood_mul_pos hU_open hgrad_cont hx₀.2 (hU_grad x₀ hx₀.2)
  let W' : Set (EuclideanSpace ℝ (Fin (n + 1))) := W ∩ interior L₀
  have hW'_open : IsOpen W' := hW_open.inter isOpen_interior
  have hx₀W' : x₀ ∈ W' := ⟨hx₀W, hx₀L₀⟩
  have hx₀_subsetW' :
      ({x₀} : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ W' := by
    intro y hy
    have hy_eq : y = x₀ := by simpa using hy
    simpa [hy_eq] using hx₀W'
  obtain ⟨L, hL_compact, hx₀L, hLW'⟩ :=
    exists_compact_between isCompact_singleton hW'_open hx₀_subsetW'
  refine ⟨σ, L, C, ψ, hσ_cases, hL_compact, hx₀L (by simp), ?_, hC_compact, hC_convex,
    hψ_cont, ?_, ?_⟩
  · intro x hx
    exact hW_subset (hLW' hx).1
  · intro x hx
    exact hgraph ⟨hx.1, interior_subset (hLW' hx.2).2⟩
  · intro x hx
    exact hW_pos x (hLW' hx).1

/-- Helper for Example 8.12: one fixed-coordinate regular frontier point admits a compact
product box in the split coordinates on which the zero set is exactly the graph of a `C¹`
function and the distinguished gradient coordinate has a fixed sign. -/
lemma fixedCoordinateSignedGraphBox
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_open : IsOpen U)
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hU_grad : ∀ x ∈ U, gradient h_boundary.boundary.definingFunction x i ≠ 0)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
    (hx₀ : x₀ ∈ frontier E ∩ U) :
    ∃ σ : ℝ,
      ∃ C : Set (EuclideanSpace ℝ (Fin n)),
      ∃ T : Set ℝ,
      ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        (σ = 1 ∨ σ = -1) ∧
        IsCompact C ∧
        Convex ℝ C ∧
        IsCompact T ∧
        Convex ℝ T ∧
        ContDiffOn ℝ 1 ψ C ∧
        (∀ z ∈ C, ψ z ∈ T) ∧
        removeCoordinateMap i x₀ ∈ interior (C ×ˢ T) ∧
        insertCoordinateMap i '' (C ×ˢ T) ⊆ U ∧
        (∀ p ∈ C ×ˢ T,
          h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
            ψ p.1 = p.2) ∧
        ∀ p ∈ C ×ˢ T,
          0 < σ * gradient h_boundary.boundary.definingFunction (insertCoordinateMap i p) i := by
  -- Route correction: keep the implicit-function product neighborhood itself so later chartwise
  -- flux arguments can rewrite the local zero set without rebuilding the chart.
  let f := h_boundary.boundary.definingFunction
  let u₀ := removeCoordinateMap i x₀
  let F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := f ∘ insertCoordinateMap i
  have hx₀Ω : x₀ ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := hU_subset hx₀.2
  have hx₀_zero : f x₀ = 0 := by
    -- Frontier points lie on the zero set of the defining function.
    have hx₀_front' : x₀ ∈ frontier E := hx₀.1
    rw [h_boundary.boundary.frontier_eq_zeroSet] at hx₀_front'
    exact hx₀_front'.2
  have hu₀_insert : insertCoordinateMap i u₀ = x₀ := by
    -- The fixed-coordinate insertion chart recovers the original frontier point.
    simpa [u₀] using insertCoordinateMap_removeCoordinateMap i x₀
  have hF_u₀_zero : F u₀ = 0 := by
    -- The pulled-back defining function also vanishes at the base point.
    simpa [F, hu₀_insert] using hx₀_zero
  have hgrad_cont :
      ContinuousOn
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          gradient h_boundary.boundary.definingFunction x i)
        U := by
    -- The distinguished gradient coordinate is continuous on the regular patch.
    exact
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 1) => ℝ) i).comp_continuousOn
        ((h_boundary.contDiffOn_gradient hU_open hU_subset).continuousOn)
  obtain ⟨σ, hσ_cases, W, hW_open, hx₀W, hW_subset, hW_pos⟩ :=
    existsSignedNeighborhood_mul_pos hU_open hgrad_cont hx₀.2 (hU_grad x₀ hx₀.2)
  have hF_contDiffAt : ContDiffAt ℝ 2 F u₀ := by
    have hf_contDiffAt : ContDiffAt ℝ 2 f x₀ := by
      -- Restrict the ambient `C²` defining function to the chosen frontier point.
      exact h_boundary.boundary.contDiffOn_definingFunction.contDiffAt (Ω.2.mem_nhds hx₀Ω)
    have hf_insert_contDiffAt : ContDiffAt ℝ 2 f (insertCoordinateMap i u₀) := by
      simpa [hu₀_insert] using hf_contDiffAt
    -- Compose the defining function with the fixed-coordinate insertion chart.
    simpa [F, f] using
      hf_insert_contDiffAt.comp u₀ (contDiff_insertCoordinateMap i).contDiffAt
  have hF_fderiv_eq :
      fderiv ℝ F u₀ = fderiv ℝ f x₀ ∘L insertCoordinateMap i := by
    have hf_hasFDerivAt : HasFDerivAt f (fderiv ℝ f x₀) x₀ := by
      -- The defining function is differentiable at the frontier base point.
      exact ((h_boundary.boundary.contDiffOn_definingFunction.contDiffAt
        (Ω.2.mem_nhds hx₀Ω)).differentiableAt (by norm_num)).hasFDerivAt
    have hf_insert_hasFDerivAt :
        HasFDerivAt f (fderiv ℝ f x₀) (insertCoordinateMap i u₀) := by
      simpa [hu₀_insert] using hf_hasFDerivAt
    have hcomp :
        HasFDerivAt F (fderiv ℝ f x₀ ∘L insertCoordinateMap i) u₀ := by
      -- Chain the defining-function derivative with the linear chart insertion.
      simpa [F, f] using
        hf_insert_hasFDerivAt.comp u₀ (insertCoordinateMap i).hasFDerivAt
    exact hcomp.fderiv
  have hF_inr_eq :
      fderiv ℝ F u₀ ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ =
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (gradient f x₀ i) := by
    apply ContinuousLinearMap.ext
    intro t
    -- Evaluate the vertical partial derivative through the distinguished gradient coordinate.
    calc
      (fderiv ℝ F u₀ ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ) t
        = fderiv ℝ f x₀ (insertCoordinateMap i (0, t)) := by
            simp [hF_fderiv_eq]
      _ = gradient f x₀ i * t := by
            simpa [f] using
              fderiv_definingFunction_insertCoordinateMap_zero h_boundary i x₀ t
      _ =
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (gradient f x₀ i)) t := by
            simp [ContinuousLinearMap.smulRight_apply, mul_comm]
  have hgrad_ne : gradient f x₀ i ≠ 0 := hU_grad x₀ hx₀.2
  have hF_inr_invertible :
      (fderiv ℝ F u₀ ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ).IsInvertible := by
    let g : ℝ →L[ℝ] ℝ :=
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((gradient f x₀ i)⁻¹)
    have hsmul_invertible :
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (gradient f x₀ i)).IsInvertible := by
      refine ContinuousLinearMap.IsInvertible.of_inverse (g := g) ?_ ?_
      · ext t
        simp [g, ContinuousLinearMap.smulRight_apply, mul_assoc, hgrad_ne, mul_comm, mul_left_comm]
      · ext t
        simp [g, ContinuousLinearMap.smulRight_apply, mul_assoc, hgrad_ne, mul_comm, mul_left_comm]
    simpa [hF_inr_eq] using hsmul_invertible
  let ψ := hF_contDiffAt.implicitFunction (pn := by norm_num) hF_inr_invertible
  have hψ_contDiffAt : ContDiffAt ℝ 1 ψ u₀.1 := by
    -- The implicit chart inherits `C¹` regularity from the defining equation.
    exact
      (hF_contDiffAt.contDiffAt_implicitFunction (pn := by norm_num) hF_inr_invertible).of_le
        (by norm_num)
  obtain ⟨Bψ, hBψ_nhds, hψ_contDiffOn⟩ :=
    hψ_contDiffAt.contDiffOn (m := 1) le_rfl (by simp)
  have hgraphEq_nhds :
      {p : EuclideanSpace ℝ (Fin n) × ℝ | F p = 0 ↔ ψ p.1 = p.2} ∈ nhds u₀ := by
    -- Near `u₀`, the zero set of `F` is exactly the graph of the implicit function.
    filter_upwards
        [hF_contDiffAt.eventually_apply_eq_iff_implicitFunction
          (pn := by norm_num) hF_inr_invertible] with p hp
    simpa [hF_u₀_zero]
      using hp
  have hψ_self : ψ u₀.1 = u₀.2 := by
    -- The implicit graph passes through the original frontier point.
    simpa [ψ, u₀] using
      hF_contDiffAt.implicitFunction_apply_self (pn := by norm_num) hF_inr_invertible
  have hpreimageW_nhds :
      insertCoordinateMap i ⁻¹' W ∈ nhds u₀ := by
    -- Shrink the product neighborhood so the signed gradient keeps the same orientation.
    have hpreimageW_open : IsOpen (insertCoordinateMap i ⁻¹' W) := by
      exact hW_open.preimage (insertCoordinateMap i).continuous
    have hu₀_mem_preimageW : u₀ ∈ insertCoordinateMap i ⁻¹' W := by
      change insertCoordinateMap i u₀ ∈ W
      simpa [hu₀_insert] using hx₀W
    exact hpreimageW_open.mem_nhds hu₀_mem_preimageW
  have hprod_nhds :
      ({p : EuclideanSpace ℝ (Fin n) × ℝ | F p = 0 ↔ ψ p.1 = p.2} ∩
        insertCoordinateMap i ⁻¹' W) ∈ nhds u₀ := by
    exact Filter.inter_mem hgraphEq_nhds hpreimageW_nhds
  obtain ⟨s, hs_nhds, t, ht_nhds, hst_subset⟩ :=
    mem_nhds_prod_iff.mp hprod_nhds
  have hst_graph :
      s ×ˢ t ⊆ {p : EuclideanSpace ℝ (Fin n) × ℝ | F p = 0 ↔ ψ p.1 = p.2} := by
    intro p hp
    exact (hst_subset hp).1
  have hst_preimageW :
      s ×ˢ t ⊆ insertCoordinateMap i ⁻¹' W := by
    intro p hp
    exact (hst_subset hp).2
  obtain ⟨r₁, hr₁_pos, hr₁_subset⟩ :=
    Metric.mem_nhds_iff.mp
      (show s ∩ Bψ ∈ nhds u₀.1 from Filter.inter_mem hs_nhds hBψ_nhds)
  obtain ⟨r₂, hr₂_pos, hr₂_subset⟩ := Metric.mem_nhds_iff.mp ht_nhds
  have hψ_contAt : ContinuousAt ψ u₀.1 := hψ_contDiffAt.continuousAt
  have hr₂_half_pos : 0 < r₂ / 2 := by linarith
  have hψ_preimageBall :
      ψ ⁻¹' Metric.ball u₀.2 (r₂ / 2) ∈ nhds u₀.1 := by
    -- Shrink the horizontal neighborhood so the graph height stays inside the vertical interval.
    simpa [hψ_self] using
      hψ_contAt.preimage_mem_nhds (Metric.ball_mem_nhds (ψ u₀.1) hr₂_half_pos)
  obtain ⟨r₃, hr₃_pos, hr₃_subset⟩ := Metric.mem_nhds_iff.mp hψ_preimageBall
  have hball_subset_s : Metric.ball u₀.1 r₁ ⊆ s := by
    intro z hz
    exact (hr₁_subset hz).1
  have hball_subset_Bψ : Metric.ball u₀.1 r₁ ⊆ Bψ := by
    intro z hz
    exact (hr₁_subset hz).2
  let C : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall u₀.1 (min r₁ r₃ / 2)
  let T : Set ℝ := Metric.closedBall u₀.2 (r₂ / 2)
  have hrmin_pos : 0 < min r₁ r₃ := lt_min hr₁_pos hr₃_pos
  have hhalf_r₁ : min r₁ r₃ / 2 < r₁ := by
    have hhalf_lt_min : min r₁ r₃ / 2 < min r₁ r₃ := by linarith
    exact lt_of_lt_of_le hhalf_lt_min (min_le_left _ _)
  have hhalf_r₃ : min r₁ r₃ / 2 < r₃ := by
    have hhalf_lt_min : min r₁ r₃ / 2 < min r₁ r₃ := by linarith
    exact lt_of_lt_of_le hhalf_lt_min (min_le_right _ _)
  have hhalf_r₂ : r₂ / 2 < r₂ := by linarith
  have hC_subset_s : C ⊆ s := by
    intro z hz
    exact hball_subset_s (Metric.closedBall_subset_ball hhalf_r₁ hz)
  have hC_subset_Bψ : C ⊆ Bψ := by
    intro z hz
    exact hball_subset_Bψ (Metric.closedBall_subset_ball hhalf_r₁ hz)
  have hψ_memT : ∀ z ∈ C, ψ z ∈ T := by
    intro z hz
    have hz_ball : z ∈ Metric.ball u₀.1 r₃ := Metric.closedBall_subset_ball hhalf_r₃ hz
    have hzψ_lt : dist (ψ z) u₀.2 < r₂ / 2 := by
      simpa [Metric.mem_ball] using hr₃_subset hz_ball
    exact Metric.mem_closedBall.2 (le_of_lt hzψ_lt)
  have hT_subset_t : T ⊆ t := by
    intro τ hτ
    exact hr₂_subset (Metric.closedBall_subset_ball hhalf_r₂ hτ)
  have hCT_subset :
      C ×ˢ T ⊆ s ×ˢ t := Set.prod_mono hC_subset_s hT_subset_t
  have hu₀_mem_interiorC : u₀.1 ∈ interior C := by
    -- The base coordinate lies in the interior of the compact closed ball.
    have hr₁_half_pos : 0 < min r₁ r₃ / 2 := by linarith
    rw [mem_interior_iff_mem_nhds]
    exact Metric.closedBall_mem_nhds u₀.1 hr₁_half_pos
  have hu₀_mem_interiorT : u₀.2 ∈ interior T := by
    -- The vertical coordinate also lies in the interior of its compact interval.
    have hr₂_half_pos : 0 < r₂ / 2 := by linarith
    rw [mem_interior_iff_mem_nhds]
    exact Metric.closedBall_mem_nhds u₀.2 hr₂_half_pos
  have hu₀_mem_interiorProd : u₀ ∈ interior (C ×ˢ T) := by
    -- Product interiors split coordinatewise for the compact box.
    rw [interior_prod_eq]
    exact ⟨hu₀_mem_interiorC, hu₀_mem_interiorT⟩
  refine ⟨σ, C, T, ψ, hσ_cases, ?_, ?_, ?_, ?_, hψ_contDiffOn.mono hC_subset_Bψ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [C] using isCompact_closedBall u₀.1 (min r₁ r₃ / 2)
  · simpa [C] using convex_closedBall u₀.1 (min r₁ r₃ / 2)
  · simpa [T] using isCompact_closedBall u₀.2 (r₂ / 2)
  · simpa [T] using convex_closedBall u₀.2 (r₂ / 2)
  · exact hψ_memT
  · simpa [u₀] using hu₀_mem_interiorProd
  · intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    exact hW_subset (hst_preimageW (hCT_subset hp))
  · intro p hp
    exact hst_graph (hCT_subset hp)
  · intro p hp
    exact hW_pos _ (hst_preimageW (hCT_subset hp))

/-- Helper for Example 8.12: on a signed graph box, frontier membership is exactly the
graph equation `t = ψ z`. -/
lemma memFrontier_insertCoordinateMap_iff_eq_of_graphBox
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hbox_subsetU : insertCoordinateMap i '' (C ×ˢ T) ⊆ U)
    (hzero_graph :
      ∀ p ∈ C ×ˢ T,
        h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
          ψ p.1 = p.2)
    {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ C ×ˢ T) :
    insertCoordinateMap i p ∈ frontier E ↔ ψ p.1 = p.2 := by
  have hpΩ : insertCoordinateMap i p ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The whole graph box stays inside the ambient domain `Ω`.
    exact hU_subset (hbox_subsetU ⟨p, hp, rfl⟩)
  constructor
  · intro hp_frontier
    -- Frontier points lie on the zero set, which is exactly the local graph.
    have hp_zero : h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 := by
      rw [h_boundary.boundary.frontier_eq_zeroSet] at hp_frontier
      exact hp_frontier.2
    exact (hzero_graph p hp).mp hp_zero
  · intro hp_graph
    -- Conversely, the graph equation gives a zero of the defining function inside `Ω`.
    rw [h_boundary.boundary.frontier_eq_zeroSet]
    exact ⟨hpΩ, (hzero_graph p hp).mpr hp_graph⟩

/-- Helper for Example 8.12: the vertical slice through fixed split coordinates
has the stable ambient derivative spelling needed for later chain rules. -/
lemma fixedCoordinateVerticalSlice_hasDerivAt
    {n : ℕ}
    (i : Fin (n + 1))
    (z : EuclideanSpace ℝ (Fin n))
    (τ : ℝ) :
    HasDerivAt (fun s : ℝ ↦ insertCoordinateMap i (z, s))
      (insertCoordinateMap i ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))) τ := by
  -- Route correction: pay the product-to-ambient derivative transport once here
  -- instead of rebuilding the pair-path argument inside `fixedCoordinateSignComparison`.
  have hpair_deriv :
      HasDerivAt (fun s : ℝ ↦ (z, s))
        ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) τ := by
    -- The split-coordinate path is affine with constant horizontal part and unit vertical speed.
    have hconst : HasDerivAt (fun _ : ℝ ↦ z) (0 : EuclideanSpace ℝ (Fin n)) τ :=
      hasDerivAt_const τ z
    simpa using HasDerivAt.prodMk hconst (hasDerivAt_id τ)
  change HasDerivAt ((insertCoordinateMap i) ∘ fun s : ℝ ↦ (z, s))
    (insertCoordinateMap i ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))) τ
  simpa [Function.comp] using (insertCoordinateMap i).hasFDerivAt.comp_hasDerivAt τ hpair_deriv

/-- Helper for Example 8.12: along a fixed vertical slice, differentiating the
defining function reads off the distinguished gradient coordinate. -/
lemma fixedCoordinateDefiningFunctionSlice_hasDerivAt
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {z : EuclideanSpace ℝ (Fin n)}
    {τ : ℝ}
    (hτΩ : insertCoordinateMap i (z, τ) ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    HasDerivAt
      (fun s : ℝ ↦ h_boundary.boundary.definingFunction (insertCoordinateMap i (z, s)))
      (gradient h_boundary.boundary.definingFunction (insertCoordinateMap i (z, τ)) i) τ := by
  let f := h_boundary.boundary.definingFunction
  have hslice_base :
      HasDerivAt (fun s : ℝ ↦ f (insertCoordinateMap i (z, s)))
        (gradient f (insertCoordinateMap i (z, τ)) i) τ := by
    -- Route correction: use the named vertical-slice derivative helper and pay
    -- the `insertCoordinateMap` transport exactly once.
    have hf_hasFDerivAt :
        HasFDerivAt f (fderiv ℝ f (insertCoordinateMap i (z, τ)))
          (insertCoordinateMap i (z, τ)) := by
      -- The ambient defining function is differentiable at every point of `Ω`.
      exact
        ((h_boundary.boundary.contDiffOn_definingFunction.contDiffAt
          (Ω.2.mem_nhds hτΩ)).differentiableAt (by norm_num)).hasFDerivAt
    have hraw :
        HasDerivAt (fun s : ℝ ↦ f (insertCoordinateMap i (z, s)))
          ((fderiv ℝ f (insertCoordinateMap i (z, τ)))
            (insertCoordinateMap i ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)))) τ := by
      exact
        hf_hasFDerivAt.comp_hasDerivAt τ
          (fixedCoordinateVerticalSlice_hasDerivAt i z τ)
    have hcoord :
        (fderiv ℝ f (insertCoordinateMap i (z, τ)))
            (insertCoordinateMap i ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))) =
          gradient f (insertCoordinateMap i (z, τ)) i := by
      simpa [f] using
        fderiv_definingFunction_insertCoordinateMap_zero h_boundary i
          (insertCoordinateMap i (z, τ)) (1 : ℝ)
    simpa [hcoord] using hraw
  have hf_hasFDerivAt :
      HasDerivAt (fun s : ℝ ↦ f (insertCoordinateMap i (z, s)))
        (gradient f (insertCoordinateMap i (z, τ)) i) τ := hslice_base
  simpa [f] using hf_hasFDerivAt

/-- Helper for Example 8.12: positive signed distinguished gradient on one
vertical fiber makes the signed defining-function slice strictly monotone. -/
lemma fixedCoordinateSignedSliceStrictMono
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {σ : ℝ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    (hT_convex : Convex ℝ T)
    (hbox_subsetU : insertCoordinateMap i '' (C ×ˢ T) ⊆ U)
    (hsign :
      ∀ p ∈ C ×ˢ T,
        0 < σ * gradient h_boundary.boundary.definingFunction (insertCoordinateMap i p) i)
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ C) :
    StrictMonoOn
      (fun τ : ℝ ↦
        σ * h_boundary.boundary.definingFunction (insertCoordinateMap i (z, τ)))
      T := by
  let f := h_boundary.boundary.definingFunction
  let g : ℝ → ℝ := fun τ ↦ σ * f (insertCoordinateMap i (z, τ))
  have hslice_deriv :
      ∀ τ ∈ T,
        HasDerivAt g (σ * gradient f (insertCoordinateMap i (z, τ)) i) τ := by
    intro τ hτ
    have hτΩ : insertCoordinateMap i (z, τ) ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
      exact hU_subset (hbox_subsetU ⟨(z, τ), ⟨hz, hτ⟩, rfl⟩)
    have hbase :=
      fixedCoordinateDefiningFunctionSlice_hasDerivAt
        (h_boundary := h_boundary) (i := i) (z := z) (τ := τ) hτΩ
    -- Differentiate the pulled-back defining function first, then scale by `σ`.
    simpa [g] using hbase.const_mul σ
  have hg_cont : ContinuousOn g T := by
    -- The signed slice is continuous because it is differentiable at every point of `T`.
    intro τ hτ
    exact (hslice_deriv τ hτ).continuousAt.continuousWithinAt
  -- Route correction: keep the monotonicity step sign-agnostic and consume only
  -- the positivity hypothesis for the signed distinguished derivative.
  refine strictMonoOn_of_deriv_pos hT_convex hg_cont ?_
  intro τ hτ
  change 0 < deriv g τ
  have hτ_deriv :
      deriv g τ = σ * gradient f (insertCoordinateMap i (z, τ)) i := by
    exact (hslice_deriv τ (interior_subset hτ)).deriv
  simpa [hτ_deriv] using hsign (z, τ) ⟨hz, interior_subset hτ⟩

/-- Helper for Example 8.12: on a signed graph box, membership in `E` is
equivalent to the signed subgraph inequality. -/
lemma fixedCoordinateSignComparison
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {σ : ℝ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hσ_cases : σ = 1 ∨ σ = -1)
    (hT_convex : Convex ℝ T)
    (hbox_subsetU : insertCoordinateMap i '' (C ×ˢ T) ⊆ U)
    (hψ_memT : ∀ z ∈ C, ψ z ∈ T)
    (hzero_graph :
      ∀ p ∈ C ×ˢ T,
        h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
          ψ p.1 = p.2)
    (hsign :
      ∀ p ∈ C ×ˢ T,
        0 < σ * gradient h_boundary.boundary.definingFunction (insertCoordinateMap i p) i)
    {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ C ×ˢ T) :
    insertCoordinateMap i p ∈ E ↔ σ * (p.2 - ψ p.1) ≤ 0 := by
  let f := h_boundary.boundary.definingFunction
  let g : ℝ → ℝ := fun τ ↦ σ * f (insertCoordinateMap i (p.1, τ))
  have hpC : p.1 ∈ C := hp.1
  have hpT : p.2 ∈ T := hp.2
  have hgraph_mem : (p.1, ψ p.1) ∈ C ×ˢ T := ⟨hpC, hψ_memT p.1 hpC⟩
  have hpΩ : insertCoordinateMap i p ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The signed graph box stays inside the ambient open set `Ω`.
    exact hU_subset (hbox_subsetU ⟨p, hp, rfl⟩)
  have hg_strict : StrictMonoOn g T := by
    -- Route correction: consume the named slice-monotonicity helper instead of
    -- rebuilding the derivative transport inline.
    simpa [g, f] using
      fixedCoordinateSignedSliceStrictMono h_boundary i hU_subset hT_convex hbox_subsetU hsign hpC
  have hg_monotone : MonotoneOn g T := hg_strict.monotoneOn
  have hgraph_zero : f (insertCoordinateMap i (p.1, ψ p.1)) = 0 := by
    exact (hzero_graph (p.1, ψ p.1) hgraph_mem).mpr rfl
  have hroot : g (ψ p.1) = 0 := by
    -- The graph height is the unique zero of the signed slice on the box.
    simp [g, hgraph_zero]
  have hmemE :
      insertCoordinateMap i p ∈ E ↔ f (insertCoordinateMap i p) ≤ 0 := by
    -- On the box, `E` is exactly the nonpositive sublevel set of the defining function.
    rw [h_boundary.boundary.interior_eq_nonpos]
    exact and_iff_right hpΩ
  rcases hσ_cases with hσ | hσ
  · constructor
    · intro hpE
      subst σ
      have hf_nonpos : f (insertCoordinateMap i p) ≤ 0 := hmemE.mp hpE
      by_contra hside
      have hlt : ψ p.1 < p.2 := by linarith
      have hpos : 0 < g p.2 := by
        simpa [hroot] using hg_strict (hψ_memT p.1 hpC) hpT hlt
      have hf_pos : 0 < f (insertCoordinateMap i p) := by simpa [g] using hpos
      linarith
    · intro hside
      subst σ
      have hle : p.2 ≤ ψ p.1 := by linarith
      have hgle : g p.2 ≤ g (ψ p.1) := hg_monotone hpT (hψ_memT p.1 hpC) hle
      have hf_nonpos : f (insertCoordinateMap i p) ≤ 0 := by
        simpa [g, hgraph_zero] using hgle
      exact hmemE.mpr hf_nonpos
  · constructor
    · intro hpE
      subst σ
      have hf_nonpos : f (insertCoordinateMap i p) ≤ 0 := hmemE.mp hpE
      have hg_nonneg : 0 ≤ g p.2 := by simpa [g] using neg_nonneg.mpr hf_nonpos
      by_contra hside
      have hlt : p.2 < ψ p.1 := by linarith
      have hneg : g p.2 < 0 := by simpa [hroot] using hg_strict hpT (hψ_memT p.1 hpC) hlt
      linarith
    · intro hside
      subst σ
      have hle : ψ p.1 ≤ p.2 := by linarith
      have hgle : g (ψ p.1) ≤ g p.2 := hg_monotone (hψ_memT p.1 hpC) hpT hle
      have hg_nonneg : 0 ≤ g p.2 := by simpa [hroot] using hgle
      have hf_nonpos : f (insertCoordinateMap i p) ≤ 0 := by
        simpa [g] using hg_nonneg
      exact hmemE.mpr hf_nonpos

/-- Helper for Example 8.12: a chart sign chosen from `{1, -1}` has square `1`. -/
lemma signedChartSign_sq_eq_one
    {σ : ℝ}
    (hσ_cases : σ = 1 ∨ σ = -1) :
    σ * σ = 1 := by
  -- The chart orientation sign is always one of the two unit values.
  rcases hσ_cases with hσ | hσ <;> simp [hσ]

/-- Helper for Example 8.12: a chart sign chosen from `{1, -1}` is nonzero. -/
lemma signedChartSign_ne_zero
    {σ : ℝ}
    (hσ_cases : σ = 1 ∨ σ = -1) :
    σ ≠ 0 := by
  -- The sign normalization excludes the degenerate case needed by later cancellation steps.
  rcases hσ_cases with hσ | hσ <;> simp [hσ]

/-- Helper for Example 8.12: the pure signed graph shear on product coordinates is injective. -/
lemma graphShear_injective
    {n : ℕ}
    {σ : ℝ}
    (hσ_cases : σ = 1 ∨ σ = -1)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) :
    Function.Injective
      (fun q : EuclideanSpace ℝ (Fin n) × ℝ ↦
        (q.1, ψ q.1 + σ * q.2)) := by
  intro q r hqr
  have hpair_inj : q.1 = r.1 ∧ ψ q.1 + σ * q.2 = ψ r.1 + σ * r.2 := by
    exact Prod.mk.inj hqr
  have hfst : q.1 = r.1 := hpair_inj.1
  have hsnd : ψ q.1 + σ * q.2 = ψ r.1 + σ * r.2 := hpair_inj.2
  have hsecond : q.2 = r.2 := by
    -- Once the base coordinates agree, the sign normalization cancels the vertical shear.
    have hsnd' : σ * q.2 = σ * r.2 := by
      simpa [hfst] using hsnd
    rcases hσ_cases with hσ | hσ
    · subst σ
      simpa using hsnd'
    · subst σ
      simpa using hsnd'
  exact Prod.ext hfst hsecond

/-- Helper for Example 8.12: the signed graph shear used in one chart is injective. -/
lemma insertCoordinateMap_graphShear_injective
    {n : ℕ}
    (i : Fin (n + 1))
    {σ : ℝ}
    (hσ_cases : σ = 1 ∨ σ = -1)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) :
    Function.Injective
      (fun q : EuclideanSpace ℝ (Fin n) × ℝ ↦
        insertCoordinateMap i (q.1, ψ q.1 + σ * q.2)) := by
  intro q r hqr
  have hpairs :
      (q.1, ψ q.1 + σ * q.2) = (r.1, ψ r.1 + σ * r.2) := by
    -- Remove the distinguished coordinate to compare the two chart coordinates directly.
    simpa [removeCoordinateMap_insertCoordinateMap] using
      congrArg (removeCoordinateMap i) hqr
  -- Route correction: factor the cancellation through the pure product-coordinate shear once,
  -- instead of reproving the same sign argument inside every charted map.
  exact graphShear_injective hσ_cases ψ hpairs

/-- Helper for Example 8.12: on a signed graph box, the chart shear rewrites membership in `E`
to the lower-half condition on the extra coordinate. -/
lemma memE_insertCoordinateMap_graphShear_iff
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {σ : ℝ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hσ_cases : σ = 1 ∨ σ = -1)
    (hT_convex : Convex ℝ T)
    (hbox_subsetU : insertCoordinateMap i '' (C ×ˢ T) ⊆ U)
    (hψ_memT : ∀ z ∈ C, ψ z ∈ T)
    (hzero_graph :
      ∀ p ∈ C ×ˢ T,
        h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
          ψ p.1 = p.2)
    (hsign :
      ∀ p ∈ C ×ˢ T,
        0 < σ * gradient h_boundary.boundary.definingFunction (insertCoordinateMap i p) i)
    {q : EuclideanSpace ℝ (Fin n) × ℝ}
    (hq : (q.1, ψ q.1 + σ * q.2) ∈ C ×ˢ T) :
    insertCoordinateMap i (q.1, ψ q.1 + σ * q.2) ∈ E ↔ q.2 ≤ 0 := by
  have hcomparison :
      insertCoordinateMap i (q.1, ψ q.1 + σ * q.2) ∈ E ↔
        σ * ((ψ q.1 + σ * q.2) - ψ q.1) ≤ 0 := by
    -- Apply the signed graph-box membership test at the sheared coordinates.
    simpa using
      (fixedCoordinateSignComparison h_boundary i hU_subset hσ_cases hT_convex
        hbox_subsetU hψ_memT hzero_graph hsign
        (p := (q.1, ψ q.1 + σ * q.2)) hq)
  -- The signed height test is exactly the lower-half-space condition in flattened coordinates.
  rcases hσ_cases with hσ | hσ
  · subst σ
    simpa using hcomparison
  · subst σ
    simpa using hcomparison

/-- Helper for Example 8.12: on a signed graph box, the chart shear lands on `frontier E`
exactly on the top face `s = 0`. -/
lemma memFrontier_insertCoordinateMap_graphShear_iff
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {σ : ℝ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hσ_cases : σ = 1 ∨ σ = -1)
    (hbox_subsetU : insertCoordinateMap i '' (C ×ˢ T) ⊆ U)
    (hzero_graph :
      ∀ p ∈ C ×ˢ T,
        h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
          ψ p.1 = p.2)
    {q : EuclideanSpace ℝ (Fin n) × ℝ}
    (hq : (q.1, ψ q.1 + σ * q.2) ∈ C ×ˢ T) :
    insertCoordinateMap i (q.1, ψ q.1 + σ * q.2) ∈ frontier E ↔ q.2 = 0 := by
  constructor
  · intro hfront
    have hgraph :
        ψ q.1 = ψ q.1 + σ * q.2 := by
      exact
        (memFrontier_insertCoordinateMap_iff_eq_of_graphBox h_boundary i hU_subset
          hbox_subsetU hzero_graph hq).1 hfront
    -- The graph equation forces the flattened coordinate to vanish.
    rcases hσ_cases with hσ | hσ
    · subst σ
      linarith
    · subst σ
      linarith
  · intro hq_zero
    -- At height `0`, the sheared chart point lies on the graph frontier.
    exact
      (memFrontier_insertCoordinateMap_iff_eq_of_graphBox h_boundary i hU_subset
        hbox_subsetU hzero_graph hq).2 (by simpa [hq_zero])

/-- Helper for Example 8.12: the signed graph shear identifies its lower-half
preimage exactly with the part of the chart box lying in `E`. -/
lemma memImage_insertCoordinateMap_graphShear_lowerHalf_iff
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {σ : ℝ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hσ_cases : σ = 1 ∨ σ = -1)
    (hT_convex : Convex ℝ T)
    (hbox_subsetU : insertCoordinateMap i '' (C ×ˢ T) ⊆ U)
    (hψ_memT : ∀ z ∈ C, ψ z ∈ T)
    (hzero_graph :
      ∀ p ∈ C ×ˢ T,
        h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
          ψ p.1 = p.2)
    (hsign :
      ∀ p ∈ C ×ˢ T,
        0 < σ * gradient h_boundary.boundary.definingFunction (insertCoordinateMap i p) i)
    {x : EuclideanSpace ℝ (Fin (n + 1))} :
    x ∈
        (fun q : EuclideanSpace ℝ (Fin n) × ℝ ↦
          insertCoordinateMap i (q.1, ψ q.1 + σ * q.2)) ''
          {q : EuclideanSpace ℝ (Fin n) × ℝ |
            (q.1, ψ q.1 + σ * q.2) ∈ C ×ˢ T ∧ q.2 ≤ 0} ↔
      x ∈ insertCoordinateMap i '' (C ×ˢ T) ∩ E := by
  have hσ_sq : σ * σ = 1 := by
    -- The sign normalization gives the explicit inverse to the graph shear.
    rcases hσ_cases with hσ | hσ <;> simp [hσ]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨(q.1, ψ q.1 + σ * q.2), hq.1, rfl⟩, ?_⟩
    -- On the lower half of the sheared chart, `memE` is exactly the sign test `q.2 ≤ 0`.
    exact
      (memE_insertCoordinateMap_graphShear_iff h_boundary i hU_subset hσ_cases hT_convex
        hbox_subsetU hψ_memT hzero_graph hsign hq.1).2 hq.2
  · rintro ⟨⟨p, hp, rfl⟩, hpE⟩
    let q : EuclideanSpace ℝ (Fin n) × ℝ := (p.1, σ * (p.2 - ψ p.1))
    have hq_eq :
        ψ p.1 + σ * (σ * (p.2 - ψ p.1)) = p.2 := by
      -- Apply the inverse shear once and collapse the resulting `σ²` factor.
      calc
        ψ p.1 + σ * (σ * (p.2 - ψ p.1))
            = ψ p.1 + (σ * σ) * (p.2 - ψ p.1) := by ring
        _ = ψ p.1 + (p.2 - ψ p.1) := by simp [hσ_sq]
        _ = p.2 := by ring
    have hq_mem : (q.1, ψ q.1 + σ * q.2) ∈ C ×ˢ T := by
      -- Reconstruct the original chart point before reading off the lower-half condition.
      change (p.1, ψ p.1 + σ * (σ * (p.2 - ψ p.1))) ∈ C ×ˢ T
      rw [hq_eq]
      exact hp
    have hq_memE :
        insertCoordinateMap i (q.1, ψ q.1 + σ * q.2) ∈ E := by
      -- The inverse shear does not change the ambient chart point.
      change insertCoordinateMap i (p.1, ψ p.1 + σ * (σ * (p.2 - ψ p.1))) ∈ E
      rw [hq_eq]
      simpa using hpE
    refine ⟨q, ⟨hq_mem, ?_⟩, ?_⟩
    · -- The membership test on `E` recovers the lower-half inequality for the inverse shear.
      exact
        (memE_insertCoordinateMap_graphShear_iff h_boundary i hU_subset hσ_cases hT_convex
          hbox_subsetU hψ_memT hzero_graph hsign hq_mem).1 hq_memE
    · -- Finish by rewriting the recovered inverse-shear point back to `p`.
      change insertCoordinateMap i (p.1, ψ p.1 + σ * (σ * (p.2 - ψ p.1))) =
        insertCoordinateMap i p
      rw [hq_eq]

/-- Helper for Example 8.12: the signed graph shear identifies its top face with
the frontier slice of the chart box. -/
lemma memImage_insertCoordinateMap_graphShear_topFace_iff
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {σ : ℝ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hσ_cases : σ = 1 ∨ σ = -1)
    (hbox_subsetU : insertCoordinateMap i '' (C ×ˢ T) ⊆ U)
    (hzero_graph :
      ∀ p ∈ C ×ˢ T,
        h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
          ψ p.1 = p.2)
    {x : EuclideanSpace ℝ (Fin (n + 1))} :
    x ∈
        (fun q : EuclideanSpace ℝ (Fin n) × ℝ ↦
          insertCoordinateMap i (q.1, ψ q.1 + σ * q.2)) ''
          {q : EuclideanSpace ℝ (Fin n) × ℝ |
            (q.1, ψ q.1 + σ * q.2) ∈ C ×ˢ T ∧ q.2 = 0} ↔
      x ∈ insertCoordinateMap i '' (C ×ˢ T) ∩ frontier E := by
  have hσ_sq : σ * σ = 1 := by
    -- The same sign normalization gives the inverse shear used for the frontier slice.
    rcases hσ_cases with hσ | hσ <;> simp [hσ]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨(q.1, ψ q.1 + σ * q.2), hq.1, rfl⟩, ?_⟩
    -- On the top face, the sheared chart point lies on `frontier E`.
    exact
      (memFrontier_insertCoordinateMap_graphShear_iff h_boundary i hU_subset hσ_cases
        hbox_subsetU hzero_graph hq.1).2 hq.2
  · rintro ⟨⟨p, hp, rfl⟩, hpFrontier⟩
    let q : EuclideanSpace ℝ (Fin n) × ℝ := (p.1, σ * (p.2 - ψ p.1))
    have hq_eq :
        ψ p.1 + σ * (σ * (p.2 - ψ p.1)) = p.2 := by
      -- Apply the inverse shear once and collapse the resulting `σ²` factor.
      calc
        ψ p.1 + σ * (σ * (p.2 - ψ p.1))
            = ψ p.1 + (σ * σ) * (p.2 - ψ p.1) := by ring
        _ = ψ p.1 + (p.2 - ψ p.1) := by simp [hσ_sq]
        _ = p.2 := by ring
    have hq_mem : (q.1, ψ q.1 + σ * q.2) ∈ C ×ˢ T := by
      -- Reconstruct the original chart point before reading off the top-face condition.
      change (p.1, ψ p.1 + σ * (σ * (p.2 - ψ p.1))) ∈ C ×ˢ T
      rw [hq_eq]
      exact hp
    have hq_frontier :
        insertCoordinateMap i (q.1, ψ q.1 + σ * q.2) ∈ frontier E := by
      -- The inverse shear preserves the ambient chart point on the frontier as well.
      change insertCoordinateMap i (p.1, ψ p.1 + σ * (σ * (p.2 - ψ p.1))) ∈ frontier E
      rw [hq_eq]
      simpa using hpFrontier
    refine ⟨q, ⟨hq_mem, ?_⟩, ?_⟩
    · -- The frontier membership now reduces exactly to the top-face equation `q.2 = 0`.
      exact
        (memFrontier_insertCoordinateMap_graphShear_iff h_boundary i hU_subset hσ_cases
          hbox_subsetU hzero_graph hq_mem).1 hq_frontier
    · -- Rewrite the inverse-shear witness back to the original chart point.
      change insertCoordinateMap i (p.1, ψ p.1 + σ * (σ * (p.2 - ψ p.1))) =
        insertCoordinateMap i p
      rw [hq_eq]

/-- Helper for Example 8.12: differentiating the local graph equation identifies the
base-coordinate tangent relation satisfied by `gradient h_boundary.boundary.definingFunction`
along the graph `z ↦ insertCoordinateMap i (z, ψ z)`. -/
lemma fixedCoordinateGraphTangentIdentity
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ_cont : ContDiffOn ℝ 1 ψ C)
    (hbox_subsetU : insertCoordinateMap i '' (C ×ˢ T) ⊆ U)
    (hψ_memT : ∀ z ∈ C, ψ z ∈ T)
    (hzero_graph :
      ∀ p ∈ C ×ˢ T,
        h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
          ψ p.1 = p.2)
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ interior C)
    (j : Fin n) :
    gradient h_boundary.boundary.definingFunction (insertCoordinateMap i (z, ψ z)) (i.succAbove j) +
        gradient h_boundary.boundary.definingFunction (insertCoordinateMap i (z, ψ z)) i *
          fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ)) =
      0 := by
  let f := h_boundary.boundary.definingFunction
  let graph : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun w ↦ insertCoordinateMap i (w, ψ w)
  let point : EuclideanSpace ℝ (Fin (n + 1)) := insertCoordinateMap i (z, ψ z)
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 : ℝ)
  let slope : ℝ := fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))
  have hzC : z ∈ C := interior_subset hz
  have hpoint_mem_box : (z, ψ z) ∈ C ×ˢ T := ⟨hzC, hψ_memT z hzC⟩
  have hpointΩ : point ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The graph point stays inside the ambient regular neighborhood.
    exact hU_subset (hbox_subsetU ⟨(z, ψ z), hpoint_mem_box, rfl⟩)
  have hC_mem_nhds : C ∈ nhds z := by
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hz) interior_subset
  have hψ_hasFDerivAt : HasFDerivAt ψ (fderiv ℝ ψ z) z := by
    -- The graph height function is differentiable at interior points of the base box.
    exact ((hψ_cont.contDiffAt hC_mem_nhds).differentiableAt (by norm_num)).hasFDerivAt
  have hpair_hasFDerivAt :
      HasFDerivAt
        (fun w : EuclideanSpace ℝ (Fin n) ↦ (w, ψ w))
        ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).prod (fderiv ℝ ψ z))
        z := by
    -- Differentiate the product graph map before inserting it back into the ambient space.
    simpa using (hasFDerivAt_id z).prodMk hψ_hasFDerivAt
  have hgraph_hasFDerivAt :
      HasFDerivAt
        graph
        ((insertCoordinateMap i).comp
          ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).prod (fderiv ℝ ψ z)))
        z := by
    -- The ambient graph map is the linear insertion composed with the product graph data.
    change
      HasFDerivAt
        ((insertCoordinateMap i) ∘ fun w : EuclideanSpace ℝ (Fin n) ↦ (w, ψ w))
        ((insertCoordinateMap i).comp
          ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).prod (fderiv ℝ ψ z)))
        z
    exact (insertCoordinateMap i).hasFDerivAt.comp z hpair_hasFDerivAt
  have hf_hasFDerivAt :
      HasFDerivAt f (fderiv ℝ f point) point := by
    -- The defining function is differentiable at the graph point because the whole box lies in `Ω`.
    exact ((h_boundary.boundary.contDiffOn_definingFunction.contDiffAt
      (Ω.2.mem_nhds hpointΩ)).differentiableAt (by norm_num)).hasFDerivAt
  have hgraphZero :
      (fun w : EuclideanSpace ℝ (Fin n) ↦ f (graph w)) =ᶠ[nhds z] fun _ ↦ 0 := by
    -- On the graph, the defining function vanishes identically near interior base points.
    filter_upwards [isOpen_interior.mem_nhds hz] with w hw
    exact (hzero_graph (w, ψ w) ⟨interior_subset hw, hψ_memT w (interior_subset hw)⟩).mpr rfl
  have hzero_hasFDerivAt :
      HasFDerivAt
        (fun w : EuclideanSpace ℝ (Fin n) ↦ f (graph w))
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        z := by
    -- Replace the composite by the locally constant-zero graph equation before differentiating.
    have hconst :
        HasFDerivAt
          (fun _ : EuclideanSpace ℝ (Fin n) ↦ (0 : ℝ))
          (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          z := by
      exact
        (hasFDerivAt_const (0 : ℝ) z :
          HasFDerivAt
            (fun _ : EuclideanSpace ℝ (Fin n) ↦ (0 : ℝ))
            (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
            z)
    exact hconst.congr_of_eventuallyEq hgraphZero
  have hcomp_hasFDerivAt :
      HasFDerivAt
        (fun w : EuclideanSpace ℝ (Fin n) ↦ f (graph w))
        ((fderiv ℝ f point).comp
          ((insertCoordinateMap i).comp
            ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).prod (fderiv ℝ ψ z))))
        z := by
    -- Differentiate the defining function along the local graph parameterization.
    exact hf_hasFDerivAt.comp z hgraph_hasFDerivAt
  have hcomp_zero :
      (fderiv ℝ f point).comp
          ((insertCoordinateMap i).comp
            ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).prod (fderiv ℝ ψ z))) =
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
    -- The composite derivative vanishes because the graph equation is locally constant.
    exact hcomp_hasFDerivAt.fderiv.symm.trans hzero_hasFDerivAt.fderiv
  have happly :
      fderiv ℝ f point
          (insertCoordinateMap i (e, slope)) =
        0 := by
    -- Evaluate the vanishing composite derivative on the `j`th base basis vector.
    have happly_map :=
      congrArg
        (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦
          A e)
        hcomp_zero
    simpa [slope] using happly_map
  -- Expand the inserted tangent vector into its horizontal and vertical parts.
  calc
    gradient f point (i.succAbove j) + gradient f point i * slope
      =
        fderiv ℝ f point (insertCoordinateMap i (e, 0)) +
          fderiv ℝ f point (insertCoordinateMap i (0, slope)) := by
            rw [fderiv_definingFunction_insertCoordinateMap_single_zero h_boundary i point j,
              fderiv_definingFunction_insertCoordinateMap_zero h_boundary i point]
            simpa [f]
    _ =
        fderiv ℝ f point
          (insertCoordinateMap i (e, 0) +
            insertCoordinateMap i (0, slope)) := by
              symm
              exact map_add _ _ _
    _ =
        fderiv ℝ f point
          (insertCoordinateMap i
            ((e, 0) + (0, slope))) := by
              rw [(insertCoordinateMap i).map_add]
    _ = fderiv ℝ f point (insertCoordinateMap i (e, slope)) := by
          simp [slope]
    _ = 0 := happly

/-- Helper for Example 8.12: on the local graph boundary, multiplying the outward-normal
pairing by `‖∇f‖` removes the normalization and leaves the tangent-corrected ambient
gradient density. -/
lemma graphBoundaryPairing_mul_norm_eq_tangentDensity
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ_cont : ContDiffOn ℝ 1 ψ C)
    (hbox_subsetU : insertCoordinateMap i '' (C ×ˢ T) ⊆ U)
    (hψ_memT : ∀ z ∈ C, ψ z ∈ T)
    (hzero_graph :
      ∀ p ∈ C ×ˢ T,
        h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
          ψ p.1 = p.2)
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ interior C) :
    ‖gradient h_boundary.boundary.definingFunction (insertCoordinateMap i (z, ψ z))‖ *
        inner ℝ
          (φ (insertCoordinateMap i (z, ψ z)))
          (h_boundary.outwardNormal (insertCoordinateMap i (z, ψ z))) =
      gradient h_boundary.boundary.definingFunction (insertCoordinateMap i (z, ψ z)) i *
        ((φ (insertCoordinateMap i (z, ψ z))) i -
          ∑ j : Fin n,
            (φ (insertCoordinateMap i (z, ψ z))) (i.succAbove j) *
              fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) := by
  let f := h_boundary.boundary.definingFunction
  let point : EuclideanSpace ℝ (Fin (n + 1)) := insertCoordinateMap i (z, ψ z)
  have hzC : z ∈ C := interior_subset hz
  have hpoint_mem_box : (z, ψ z) ∈ C ×ˢ T := ⟨hzC, hψ_memT z hzC⟩
  have hpoint_frontier : point ∈ frontier E := by
    -- The graph equation puts the distinguished graph point on the frontier.
    exact
      (memFrontier_insertCoordinateMap_iff_eq_of_graphBox
        h_boundary i hU_subset hbox_subsetU hzero_graph hpoint_mem_box).2 rfl
  have hgrad_ne : gradient f point ≠ 0 := by
    -- Frontier regularity first gives `fderiv ≠ 0`, and `toDual_gradient` transports this to
    -- the gradient spelling used by the boundary density.
    intro hgrad_zero
    have hfderiv_zero : fderiv ℝ f point = 0 := by
      rw [← toDual_gradient (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin (n + 1))) (f := f) (x := point),
        hgrad_zero]
      simp
    exact h_boundary.boundary.regular_on_frontier point hpoint_frontier hfderiv_zero
  have hnormalize :
      ‖gradient f point‖ * inner ℝ (φ point) (h_boundary.outwardNormal point) =
        inner ℝ (φ point) (gradient f point) := by
    -- Replace the outward normal by the normalized gradient and cancel the scalar factor.
    have hnormal :
        h_boundary.outwardNormal point =
          ((‖gradient f point‖)⁻¹ : ℝ) • gradient f point := by
      symm
      simpa [f] using
        normalizedGradient_eq_outwardNormal_onFrontier h_boundary hpoint_frontier
    calc
      ‖gradient f point‖ * inner ℝ (φ point) (h_boundary.outwardNormal point)
        = ‖gradient f point‖ * (‖gradient f point‖⁻¹ * inner ℝ (φ point) (gradient f point)) := by
            rw [hnormal, real_inner_smul_right]
      _ = (‖gradient f point‖ * ‖gradient f point‖⁻¹) * inner ℝ (φ point) (gradient f point) := by
            ring
      _ = inner ℝ (φ point) (gradient f point) := by
            rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hgrad_ne), one_mul]
  have hsplit :
      inner ℝ (φ point) (gradient f point) =
        (φ point) i * gradient f point i +
          ∑ j : Fin n, (φ point) (i.succAbove j) * gradient f point (i.succAbove j) := by
    -- Split the Euclidean inner product into the distinguished coordinate and the remaining
    -- `succAbove` coordinates.
    rw [PiLp.inner_apply]
    calc
      ∑ k : Fin (n + 1), gradient f point k * φ point k
        = ∑ k : Fin (n + 1), φ point k * gradient f point k := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            ring
      _ =
          (φ point) i * gradient f point i +
            ∑ j : Fin n, (φ point) (i.succAbove j) * gradient f point (i.succAbove j) := by
              rw [Fin.sum_univ_succAbove]
  have htangent :
      ∀ j : Fin n,
        gradient f point (i.succAbove j) =
          -(gradient f point i * fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) := by
    intro j
    -- The graph tangent identity rewrites each complementary gradient coordinate into the
    -- distinguished gradient coordinate times the corresponding graph slope.
    exact eq_neg_of_add_eq_zero_left <|
      fixedCoordinateGraphTangentIdentity h_boundary i hU_subset hψ_cont
        hbox_subsetU hψ_memT hzero_graph hz j
  have hfactor :
      ∑ j : Fin n,
          (φ point) (i.succAbove j) *
            (gradient f point i * fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) =
        gradient f point i *
          ∑ j : Fin n,
            (φ point) (i.succAbove j) * fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ)) := by
    -- Factor the distinguished gradient coordinate out of the tangential correction sum.
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    ring
  calc
    ‖gradient f point‖ * inner ℝ (φ point) (h_boundary.outwardNormal point)
      = inner ℝ (φ point) (gradient f point) := hnormalize
    _ =
        (φ point) i * gradient f point i +
          ∑ j : Fin n, (φ point) (i.succAbove j) * gradient f point (i.succAbove j) := hsplit
    _ =
        (φ point) i * gradient f point i -
          ∑ j : Fin n,
            (φ point) (i.succAbove j) *
              (gradient f point i * fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) := by
            -- Rewrite the complementary gradient coordinates through the graph tangent relation.
            simp_rw [htangent, mul_neg]
            rw [Finset.sum_neg_distrib]
            ring
    _ =
        gradient f point i *
          ((φ point) i -
            ∑ j : Fin n,
              (φ point) (i.succAbove j) * fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) := by
            -- Collect the common distinguished gradient coordinate into the explicit density.
            rw [show (φ point) i * gradient f point i = gradient f point i * (φ point) i by ring,
              hfactor]
            ring

/-- Helper for Example 8.12: the graph-boundary pairing from
`graphBoundaryPairing_mul_norm_eq_tangentDensity` can be recorded with the chosen sign `σ`,
producing the explicit common chart density used by the local flux theorem. -/
lemma graphBoxBoundaryDensity_mul_norm_eq_commonDensity
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {σ : ℝ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ_cont : ContDiffOn ℝ 1 ψ C)
    (hbox_subsetU : insertCoordinateMap i '' (C ×ˢ T) ⊆ U)
    (hψ_memT : ∀ z ∈ C, ψ z ∈ T)
    (hzero_graph :
      ∀ p ∈ C ×ˢ T,
        h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
          ψ p.1 = p.2)
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ interior C) :
    σ * ‖gradient h_boundary.boundary.definingFunction (insertCoordinateMap i (z, ψ z))‖ *
        inner ℝ
          (φ (insertCoordinateMap i (z, ψ z)))
          (h_boundary.outwardNormal (insertCoordinateMap i (z, ψ z))) =
      (σ * gradient h_boundary.boundary.definingFunction (insertCoordinateMap i (z, ψ z)) i) *
        ((φ (insertCoordinateMap i (z, ψ z))) i -
          ∑ j : Fin n,
            (φ (insertCoordinateMap i (z, ψ z))) (i.succAbove j) *
              fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) := by
  -- Multiply the unsigned graph density identity by the chosen chart sign `σ`.
  rw [mul_assoc,
    graphBoundaryPairing_mul_norm_eq_tangentDensity h_boundary i hU_subset hψ_cont
      hbox_subsetU hψ_memT hzero_graph φ hz]
  ring

/-- Helper for Example 8.12: on a neighborhood where one fixed gradient
coordinate never vanishes, compact frontier pieces have finite codimension-`1`
Euclidean Hausdorff measure. -/
lemma compactFrontierSurfaceMeasure_ne_top_of_fixedCoordinate
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (i : Fin (n + 1))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_open : IsOpen U)
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hU_grad : ∀ x ∈ U, gradient h_boundary.boundary.definingFunction x i ≠ 0)
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E ∩ U) :
    (MeasureTheory.Measure.euclideanHausdorffMeasure n) K ≠ ⊤ := by
  let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
    MeasureTheory.Measure.euclideanHausdorffMeasure n
  have hlocalCore :
      ∀ x : K,
        ∃ L : Set (EuclideanSpace ℝ (Fin (n + 1))),
          ∃ C : Set (EuclideanSpace ℝ (Fin n)),
          ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
            IsCompact L ∧
            (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ interior L ∧
            L ⊆ U ∧
            IsCompact C ∧
            Convex ℝ C ∧
            ContDiffOn ℝ 1 ψ C ∧
            frontier E ∩ L ⊆
              ((fun z : EuclideanSpace ℝ (Fin n) ↦
                  HasC2BoundaryIn.insertCoordinateMap i (z, ψ z)) '' C) := by
    intro x
    -- Each compact frontier point sits in one local graph core with the same fixed coordinate.
    exact fixedCoordinateFrontierGraphCore h_boundary i hU_open hU_subset hU_grad (hK_subset x.2)
  classical
  choose L C ψ hL_compact hxL hLU hC_compact hC_convex hψ_cont hgraph using hlocalCore
  have hcompactCore_cover :
      K ⊆ ⋃ x : K, interior (L x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxL ⟨x, hx⟩⟩
  obtain ⟨t, ht_cover⟩ :=
    hK_compact.elim_finite_subcover (fun x : K ↦ interior (L x))
      (fun _ ↦ isOpen_interior) hcompactCore_cover
  have hpiece_ne_top :
      ∀ x ∈ t, μ (K ∩ L x) ≠ ⊤ := by
    intro x hx
    have hpiece_subset_graph :
        K ∩ L x ⊆
          ((fun z : EuclideanSpace ℝ (Fin n) ↦
              HasC2BoundaryIn.insertCoordinateMap i (z, ψ x z)) '' C x) := by
      intro y hy
      exact hgraph x ⟨(hK_subset hy.1).1, hy.2⟩
    have hgraph_ne_top :
        μ ((fun z : EuclideanSpace ℝ (Fin n) ↦
            HasC2BoundaryIn.insertCoordinateMap i (z, ψ x z)) '' C x) ≠ ⊤ := by
      simpa [μ] using graphImage_surfaceMeasure_ne_top (hC_convex x) (hC_compact x) (hψ_cont x)
    have hpiece_le :
        μ (K ∩ L x) ≤
          μ ((fun z : EuclideanSpace ℝ (Fin n) ↦
              HasC2BoundaryIn.insertCoordinateMap i (z, ψ x z)) '' C x) := by
      exact MeasureTheory.measure_mono hpiece_subset_graph
    exact ne_of_lt <| lt_of_le_of_lt hpiece_le hgraph_ne_top.lt_top
  have hmeasure_cover_le :
      μ K ≤ t.sum (fun x ↦ μ (K ∩ L x)) := by
    have hsubset_union :
        K ⊆ ⋃ x ∈ t, K ∩ L x := by
      intro y hy
      rcases Set.mem_iUnion₂.mp (ht_cover hy) with ⟨x, hxt, hyL⟩
      exact Set.mem_iUnion₂.mpr ⟨x, hxt, ⟨hy, interior_subset hyL⟩⟩
    calc
      μ K ≤ μ (⋃ x ∈ t, K ∩ L x) := by
        exact MeasureTheory.measure_mono hsubset_union
      _ ≤ t.sum (fun x ↦ μ (K ∩ L x)) := by
        simpa using
          (MeasureTheory.measure_biUnion_finset_le (μ := μ) t
            (fun x : K ↦ K ∩ L x))
  have hsum_ne_top : t.sum (fun x ↦ μ (K ∩ L x)) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.2 hpiece_ne_top
  exact ne_of_lt <| lt_of_le_of_lt hmeasure_cover_le hsum_ne_top.lt_top

/-- Helper for Example 8.12: a compact frontier piece of a `C²` boundary has
finite codimension-`1` Euclidean Hausdorff measure. -/
lemma compactFrontierSurfaceMeasure_ne_top
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E) :
    (MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) K ≠ ⊤ := by
  cases d with
  | zero =>
      have hfrontier : frontier E = ∅ := h_boundary.frontier_eq_empty_of_zeroDim
      have hK_empty : K = ∅ := by
        -- In dimension `0`, the regular boundary is empty, so every compact frontier piece is empty.
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        simpa [hfrontier] using hK_subset hx
      simpa [hK_empty]
  | succ d =>
      obtain ⟨V, hV_open, hV_subsetΩ, hK_cover, hV_grad⟩ :=
        h_boundary.existsFiniteCoordinateGradientCoverOnCompact hK_compact hK_subset
      let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin (d + 1))) :=
        MeasureTheory.Measure.euclideanHausdorffMeasure d
      have hlocalCore :
          ∀ x : K,
            ∃ i : Fin (d + 1),
              ∃ L : Set (EuclideanSpace ℝ (Fin (d + 1))),
                IsCompact L ∧
                (x : EuclideanSpace ℝ (Fin (d + 1))) ∈ interior L ∧
                L ⊆ V i := by
        intro x
        rcases Set.mem_iUnion.mp (hK_cover x.2) with ⟨i, hxi⟩
        have hx_subset : ({(x : EuclideanSpace ℝ (Fin (d + 1)))} :
            Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ V i := by
          intro y hy
          have hy_eq : y = (x : EuclideanSpace ℝ (Fin (d + 1))) := by
            simpa using hy
          simpa [hy_eq] using hxi
        obtain ⟨L, hL_compact, hxL, hLV⟩ :=
          exists_compact_between isCompact_singleton (hV_open i) hx_subset
        refine ⟨i, L, hL_compact, ?_, hLV⟩
        exact hxL (by simp)
      classical
      choose i L hL_compact hxL hLV using hlocalCore
      have hcompactCore_cover :
          K ⊆ ⋃ x : K, interior (L x) := by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxL ⟨x, hx⟩⟩
      obtain ⟨t, ht_cover⟩ :=
        hK_compact.elim_finite_subcover (fun x : K ↦ interior (L x))
          (fun _ ↦ isOpen_interior) hcompactCore_cover
      have hpiece_ne_top :
          ∀ x ∈ t, μ (K ∩ L x) ≠ ⊤ := by
        intro x hx
        have hpiece_compact : IsCompact (K ∩ L x) := by
          exact hK_compact.inter_right (hL_compact x).isClosed
        have hpiece_subset :
            K ∩ L x ⊆ frontier E ∩ V (i x) := by
          intro y hy
          refine ⟨hK_subset hy.1, hLV x hy.2⟩
        -- Route correction: the global compact theorem now depends on one fixed-coordinate patch
        -- helper, so the only remaining blocker is chartwise implicit-function extraction.
        exact
          compactFrontierSurfaceMeasure_ne_top_of_fixedCoordinate h_boundary (i x)
            (hV_open (i x)) (hV_subsetΩ (i x))
            (fun y hy ↦ hV_grad (i x) y hy) hpiece_compact hpiece_subset
      have hmeasure_cover_le :
          μ K ≤ t.sum (fun x ↦ μ (K ∩ L x)) := by
        have hsubset_union :
            K ⊆ ⋃ x ∈ t, K ∩ L x := by
          intro y hy
          rcases Set.mem_iUnion₂.mp (ht_cover hy) with ⟨x, hxt, hyL⟩
          exact Set.mem_iUnion₂.mpr ⟨x, hxt, ⟨hy, interior_subset hyL⟩⟩
        calc
          μ K ≤ μ (⋃ x ∈ t, K ∩ L x) := by
            exact MeasureTheory.measure_mono hsubset_union
          _ ≤ t.sum (fun x ↦ μ (K ∩ L x)) := by
            simpa using
              (MeasureTheory.measure_biUnion_finset_le (μ := μ) t
                (fun x : K ↦ K ∩ L x))
      have hsum_ne_top : t.sum (fun x ↦ μ (K ∩ L x)) ≠ ⊤ := by
        exact ENNReal.sum_ne_top.2 hpiece_ne_top
      exact ne_of_lt <|
        lt_of_le_of_lt hmeasure_cover_le hsum_ne_top.lt_top

/-- Helper for Example 8.12: if a compactly supported `C¹` field stays away from
`frontier E`, then its divergence integral over `E` vanishes. -/
theorem offFrontierDivergence_eq_zero
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hφ_cont : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_subset : tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hφ_frontier_disjoint : tsupport φ ∩ frontier E = ∅) :
    ∫ x in E,
        (∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(domainMeasure Ω) = 0 := by
  let K : Set (EuclideanSpace ℝ (Fin (n + 1))) := closure (E ∩ tsupport φ)
  have hK_compact : IsCompact K := by
    -- The compact support of `φ` controls the closure of the interior core we localize around.
    exact hφ_compact.isCompact.closure_of_subset Set.inter_subset_right
  have hK_subsetInterior : K ⊆ interior E := by
    -- Frontier-disjoint support forces the `E`-part of the support into the interior.
    simpa [K] using
      h_boundary.closureInterTsupportSubsetInteriorOfFrontierDisjoint
        (φ := φ) hφ_frontier_disjoint
  obtain ⟨U, hU_open, hKU, hU_closure⟩ :=
    normal_exists_closure_subset hK_compact.isClosed isOpen_interior hK_subsetInterior
  obtain ⟨L, hL_compact, hKL, hLU⟩ :=
    exists_compact_between hK_compact hU_open hKU
  obtain ⟨χ, hχ_cont, hχ_compact, hχ_subsetU, hχ_one, _hχ_range⟩ :=
    existsContDiffCompactSupportCutoffEqOneOnCompact hU_open hL_compact hLU
  let φNear : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := χ • φ
  let φFar : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    (fun x ↦ 1 - χ x) • φ
  have hsplit : ∀ x, φ x = φFar x + φNear x := by
    -- Split `φ` into the interior-localized piece and the complementary remainder.
    intro x
    simp [φFar, φNear, sub_eq_add_neg, add_smul]
  have hφNear_cont : ContDiff ℝ 1 φNear := by
    -- Multiplying by the smooth cutoff keeps the localized field `C¹`.
    simpa [φNear] using hχ_cont.smul hφ_cont
  have hφFar_cont : ContDiff ℝ 1 φFar := by
    -- The complementary field is also `C¹`.
    simpa [φFar] using (contDiff_const.sub hχ_cont).smul hφ_cont
  have hφNear_compact : HasCompactSupport φNear := by
    -- The cutoff support controls the near field.
    simpa [φNear] using hχ_compact.smul_right (f' := φ)
  have hφFar_compact : HasCompactSupport φFar := by
    -- Compact support of `φ` controls the far field.
    simpa [φFar] using hφ_compact.smul_left (f := fun x ↦ 1 - χ x)
  have hφNear_subsetU : tsupport φNear ⊆ U := by
    -- The localized field lives where the cutoff itself lives.
    exact (tsupport_smul_subset_left χ φ).trans hχ_subsetU
  have hU_subsetΩ : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The separating neighborhood still sits inside `Ω` because its closure stays in `interior E`.
    intro x hx
    exact h_boundary.subset (interior_subset (hU_closure (subset_closure hx)))
  have hφFar_notMem_tsupport : ∀ x ∈ E, x ∉ tsupport φFar := by
    -- The thicker cutoff makes the far piece vanish on a neighborhood of every point of `E`.
    intro x hxE
    by_cases hxφ : x ∈ tsupport φ
    · have hxK : x ∈ K := subset_closure ⟨hxE, hxφ⟩
      have hxL : x ∈ interior L := hKL hxK
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [isOpen_interior.mem_nhds hxL] with y hy
      have hχy : χ y = 1 := hχ_one (interior_subset hy)
      simp [φFar, hχy]
    · rw [notMem_tsupport_iff_eventuallyEq] at hxφ
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [hxφ] with y hy
      simp [φFar, hy]
  have hφ_diff : Differentiable ℝ φ := hφ_cont.differentiable_one
  have hφNear_diff : Differentiable ℝ φNear := hφNear_cont.differentiable_one
  have hφFar_diff : Differentiable ℝ φFar := hφFar_cont.differentiable_one
  have hdiv_split :
      ∀ x,
        (∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i) =
          (∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i) +
            (∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i) := by
    intro x
    have hfd :
        fderiv ℝ φ x = fderiv ℝ φFar x + fderiv ℝ φNear x := by
      rw [show φ = fun y ↦ φFar y + φNear y by
            funext y
            exact hsplit y]
      exact fderiv_add (hφFar_diff x) (hφNear_diff x)
    -- Rewrite the divergence through linearity of the Fréchet derivative.
    simpa [Finset.sum_add_distrib] using
      congrArg
        (fun A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
            EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), A (EuclideanSpace.single i (1 : ℝ)) i)
        hfd
  have hdivFar_integrable :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i)
        (domainMeasure Ω) := by
    -- The far divergence remains integrable because the field is `C¹` with compact support.
    exact rawDivergenceIntegrable hφFar_cont hφFar_compact
  have hdivNear_integrable :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
        (domainMeasure Ω) := by
    -- The same compact-support integrability applies to the localized divergence.
    exact rawDivergenceIntegrable hφNear_cont hφNear_compact
  have hdivFar_restrict :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i)
        ((domainMeasure Ω).restrict E) :=
    hdivFar_integrable.restrict
  have hdivNear_restrict :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
        ((domainMeasure Ω).restrict E) :=
    hdivNear_integrable.restrict
  have hdivFar_zero_on_E :
      ∀ x ∈ E,
        (∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i) = 0 := by
    intro x hxE
    exact rawDivergence_eq_zero_of_notMem_tsupport (hφFar_notMem_tsupport x hxE)
  have hE_null : MeasureTheory.NullMeasurableSet E (domainMeasure Ω) := by
    have hdef_ae :
        MeasureTheory.AEStronglyMeasurable
          h_boundary.boundary.definingFunction (domainMeasure Ω) := by
      simpa [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using
        h_boundary.boundary.contDiffOn_definingFunction.continuousOn.aestronglyMeasurable
          (μ := (MeasureTheory.MeasureSpace.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin (n + 1)))))
          Ω.2.measurableSet
    -- The defining-function sublevel description makes `E` null-measurable for the restricted domain measure.
    rw [h_boundary.boundary.interior_eq_nonpos]
    exact Ω.2.measurableSet.nullMeasurableSet.inter
      (hdef_ae.nullMeasurableSet_le MeasureTheory.aestronglyMeasurable_const)
  -- Route correction: after the thick-cutoff split, the only geometric input is the
  -- interior-support divergence-zero helper for `φNear`.
  calc
    ∫ x in E,
        (∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(domainMeasure Ω)
      =
        ∫ x in E,
          ((∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i) +
            ∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x
            exact hdiv_split x
    _ =
        (∫ x in E,
          (∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω)) +
        ∫ x in E,
          (∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω) := by
            rw [MeasureTheory.integral_add hdivFar_restrict hdivNear_restrict]
    _ =
        0 +
        ∫ x in E,
          (∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω) := by
            congr 1
            have hzero_ae :
                ∀ᵐ x ∂((domainMeasure Ω).restrict E),
                  (∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i) = 0 := by
              filter_upwards [MeasureTheory.ae_restrict_mem₀ hE_null] with x hx
              exact hdivFar_zero_on_E x hx
            rw [show (∫ x in E,
                (∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i)
                ∂(domainMeasure Ω)) =
                ∫ x,
                  (∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i)
                  ∂((domainMeasure Ω).restrict E) by
                rfl]
            exact MeasureTheory.integral_eq_zero_of_ae hzero_ae
    _ =
        ∫ x in E,
          (∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω) := by
            simp
    _ = 0 := by
            refine compactlySupportedInInterior_divergence_eq_zero h_boundary hU_open hU_subsetΩ ?_
              φNear hφNear_cont hφNear_compact hφNear_subsetU
            exact hU_closure

/-- Helper for Example 8.12: a finite chart-box cover of the compact frontier-support
core can be shrunk to open pieces with compact closures, and each closure admits a
subordinate `C¹` cutoff supported in the same chart box. -/
lemma finiteCoordinateBoxShrunkCutoffs
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_open : IsOpen U)
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hU_grad : ∀ x ∈ U, gradient h_boundary.boundary.definingFunction x ≠ 0)
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hφ_cont : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_subsetU : tsupport φ ⊆ U)
    (K : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hK_def : K = frontier E ∩ tsupport φ)
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E)
    {i : K → Fin (n + 1)}
    {σ : K → ℝ}
    {C : K → Set (EuclideanSpace ℝ (Fin n))}
    {T : K → Set ℝ}
    {ψ : K → EuclideanSpace ℝ (Fin n) → ℝ}
    (hσ_cases : ∀ x : K, σ x = 1 ∨ σ x = -1)
    (hC_compact : ∀ x : K, IsCompact (C x))
    (hC_convex : ∀ x : K, Convex ℝ (C x))
    (hT_compact : ∀ x : K, IsCompact (T x))
    (hT_convex : ∀ x : K, Convex ℝ (T x))
    (hψ_cont : ∀ x : K, ContDiffOn ℝ 1 (ψ x) (C x))
    (hψ_memT : ∀ x : K, ∀ z ∈ C x, ψ x z ∈ T x)
    (hxBox : ∀ x : K,
      removeCoordinateMap (i x) (x : EuclideanSpace ℝ (Fin (n + 1))) ∈
        interior (C x ×ˢ T x))
    (hbox_subset : ∀ x : K,
      insertCoordinateMap (i x) '' (C x ×ˢ T x) ⊆
        (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hzero_graph : ∀ x : K,
      ∀ p ∈ C x ×ˢ T x,
        h_boundary.boundary.definingFunction (insertCoordinateMap (i x) p) = 0 ↔
          ψ x p.1 = p.2)
    (hsign : ∀ x : K,
      ∀ p ∈ C x ×ˢ T x,
        0 < σ x * gradient h_boundary.boundary.definingFunction
          (insertCoordinateMap (i x) p) (i x))
    {t : Finset K}
    (ht_cover : K ⊆ ⋃ x ∈ t,
      insertCoordinateMap (i x) '' interior (C x ×ˢ T x)) :
    ∃ V : {x : K // x ∈ t} → Set (EuclideanSpace ℝ (Fin (n + 1))),
      (∀ a, IsOpen (V a)) ∧
      K ⊆ ⋃ a, V a ∧
      (∀ a, IsCompact (closure (V a))) ∧
      (∀ a, closure (V a) ⊆ insertCoordinateMap (i a.1) '' interior (C a.1 ×ˢ T a.1)) ∧
      ∃ χ : {x : K // x ∈ t} → EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
        (∀ a, ContDiff ℝ 1 (χ a)) ∧
        (∀ a, HasCompactSupport (χ a)) ∧
        (∀ a, tsupport (χ a) ⊆ insertCoordinateMap (i a.1) '' interior (C a.1 ×ˢ T a.1)) ∧
        (∀ a, Set.EqOn (χ a) 1 (closure (V a))) ∧
        (∀ a y, χ a y ∈ Set.Icc (0 : ℝ) 1) := by
  let W : {x : K // x ∈ t} → Set (EuclideanSpace ℝ (Fin (n + 1))) := fun a ↦
    insertCoordinateMap (i a.1) '' interior (C a.1 ×ˢ T a.1)
  have hW_open : ∀ a, IsOpen (W a) := by
    intro a
    obtain ⟨e, he⟩ := insertCoordinateMap_isInvertible (i a.1)
    have he_fun :
        ∀ p : EuclideanSpace ℝ (Fin n) × ℝ,
          e p = insertCoordinateMap (i a.1) p := by
      intro p
      simpa using congrArg
        (fun m : EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ]
            EuclideanSpace ℝ (Fin (n + 1)) ↦
          m p) he
    have himage :
        insertCoordinateMap (i a.1) '' interior (C a.1 ×ˢ T a.1) =
          e '' interior (C a.1 ×ˢ T a.1) := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, by simpa using he_fun p⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, by simpa using (he_fun p).symm⟩
    rw [show W a = e '' interior (C a.1 ×ˢ T a.1) by simpa [W] using himage]
    -- The fixed-coordinate chart is linear, so it preserves openness of the product box.
    exact e.isOpenMap _ isOpen_interior
  have hW_cover : K ⊆ ⋃ a : {x : K // x ∈ t}, W a := by
    intro y hy
    rcases Set.mem_iUnion₂.mp (ht_cover hy) with ⟨x, hxt, hyx⟩
    exact Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, by simpa [W] using hyx⟩
  have hW_pointFinite :
      ∀ y ∈ K, {a : {x : K // x ∈ t} | y ∈ W a}.Finite := by
    intro y hy
    exact Set.toFinite _
  obtain ⟨V, hV_cover, hV_open, hV_closure_subset, hV_compact⟩ :=
    exists_subset_iUnion_closure_subset_t2space
      (s := K) hK_compact hW_open hW_pointFinite hW_cover
  choose χ hχ_cont hχ_compact hχ_subset hχ_one hχ_range using
    fun a ↦
      existsContDiffCompactSupportCutoffEqOneOnCompact
        (hW_open a) (hV_compact a) (hV_closure_subset a)
  refine ⟨V, hV_open, hV_cover, hV_compact, hV_closure_subset, χ,
    hχ_cont, hχ_compact, hχ_subset, hχ_one, hχ_range⟩

/-- Helper for Example 8.12: if a finite family of cutoffs is identically `1` on the
closures of a shrunk cover, then the product of the complementary cutoffs vanishes on a
neighborhood of each covered point. -/
lemma finiteCoordinateCutoffProduct_eventuallyEq_zero
    {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    {t : Finset K}
    {V : {x : K // x ∈ t} → Set (EuclideanSpace ℝ (Fin d))}
    {χ : {x : K // x ∈ t} → EuclideanSpace ℝ (Fin d) → ℝ}
    (hV_open : ∀ a, IsOpen (V a))
    (hV_cover : K ⊆ ⋃ a, V a)
    (hχ_one : ∀ a, Set.EqOn (χ a) 1 (closure (V a)))
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ K) :
    (fun y ↦ t.attach.prod (fun a ↦ (1 - χ a y))) =ᶠ[nhds x] 0 := by
  rcases Set.mem_iUnion.mp (hV_cover hx) with ⟨a, hxa⟩
  filter_upwards [(hV_open a).mem_nhds hxa] with y hy
  have hχ_eq_one : χ a y = 1 := hχ_one a (subset_closure hy)
  calc
    t.attach.prod (fun b ↦ (1 - χ b y))
      = (1 - χ a y) * (t.attach.erase a).prod (fun b ↦ (1 - χ b y)) := by
          symm
          exact Finset.mul_prod_erase (t.attach) (fun b ↦ 1 - χ b y)
            (by simpa using Finset.mem_attach a)
    _ = 0 := by simp [hχ_eq_one]

/-- Helper for Example 8.12: the boundary pairing of a continuous compactly
supported field is integrable along `frontier E`. -/
lemma boundaryFluxIntegrable_of_continuous_compactSupport
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hφ_cont : Continuous φ)
    (hφ_compact : HasCompactSupport φ) :
    MeasureTheory.IntegrableOn
      (fun x ↦ inner ℝ (φ x) (h_boundary.outwardNormal x))
      (frontier E)
      (MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) := by
  let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) :=
    MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)
  let g : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦
    inner ℝ (φ x) (h_boundary.outwardNormal x)
  have hg_cont : ContinuousOn g (frontier E) := by
    -- Both factors in the boundary pairing are continuous along `frontier E`.
    simpa [g] using
      hφ_cont.continuousOn.inner h_boundary.isOutwardNormal.contDiffOn_normal.continuousOn
  have hcore_compact : IsCompact (frontier E ∩ tsupport φ) := by
    -- The field only contributes on the compact frontier-support core.
    simpa [Set.inter_comm] using hφ_compact.isCompact.inter_right isClosed_frontier
  have hg_support_subset : Function.support g ⊆ tsupport φ := by
    intro x hx
    have hφ_nonzero : φ x ≠ 0 := by
      intro hφ_zero
      exact hx <| by simpa [g, hφ_zero]
    exact subset_tsupport φ hφ_nonzero
  have hcore_subset : frontier E ∩ tsupport φ ⊆ frontier E := by
    intro x hx
    exact hx.1
  have hμ_core_ne_top : μ (frontier E ∩ tsupport φ) ≠ ⊤ := by
    -- The regular boundary structure supplies finite surface measure on compact frontier patches.
    simpa [μ] using
      compactFrontierSurfaceMeasure_ne_top h_boundary hcore_compact hcore_subset
  have hg_integrable_core : MeasureTheory.IntegrableOn g (frontier E ∩ tsupport φ) μ := by
    -- Continuity on the compact core gives integrability once the surface measure is finite.
    exact
      (hg_cont.mono fun x hx ↦ hx.1).integrableOn_of_subset_isCompact
        hcore_compact hcore_compact.isClosed.measurableSet subset_rfl hμ_core_ne_top
  have hg_integrable_support :
      MeasureTheory.IntegrableOn g (frontier E ∩ Function.support g) μ := by
    -- Shrink from the field support to the actual support of the boundary integrand.
    refine hg_integrable_core.mono_set ?_
    intro x hx
    exact ⟨hx.1, hg_support_subset hx.2⟩
  -- Route correction: keep all boundary-integrability plumbing behind one helper before the
  -- near-field cutoff induction starts summing local boundary terms.
  exact MeasureTheory.IntegrableOn.of_inter_support
    isClosed_frontier.measurableSet hg_integrable_support

/-- Helper for Example 8.12: adding one more cutoff factor splits the near-field
coefficient into the previous remainder plus the new localized chart piece. -/
lemma one_sub_cutoffProduct_insert
    {α ι : Type*}
    [DecidableEq ι]
    {χ : ι → α → ℝ}
    {a : ι}
    {s : Finset ι}
    (ha : a ∉ s)
    (y : α) :
    1 - (insert a s).prod (fun b ↦ (1 - χ b y)) =
      (1 - s.prod (fun b ↦ (1 - χ b y))) + χ a y * s.prod (fun b ↦ (1 - χ b y)) := by
  -- Expand the inserted product once and collect the new cutoff contribution.
  rw [Finset.prod_insert ha]
  ring

/-- Helper for Example 8.12: the new cutoff-weighted induction piece stays `C¹`,
compactly supported, and inside the chart box indexed by `a`. -/
lemma cutoffWeightedField_chartSupport
    {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {t : Finset K}
    {i : K → Fin (n + 1)}
    {C : K → Set (EuclideanSpace ℝ (Fin n))}
    {T : K → Set ℝ}
    {χ : {x : K // x ∈ t} → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hχ_cont : ∀ a, ContDiff ℝ 1 (χ a))
    (hχ_compact : ∀ a, HasCompactSupport (χ a))
    (hχ_subset :
      ∀ a,
        tsupport (χ a) ⊆
          insertCoordinateMap (i a.1) '' interior (C a.1 ×ˢ T a.1))
    (hφ_cont : ContDiff ℝ 1 φ)
    (a : {x : K // x ∈ t})
    (s : Finset {x : K // x ∈ t}) :
    ContDiff ℝ 1 (fun y ↦ (χ a y * s.prod (fun b ↦ (1 - χ b y))) • φ y) ∧
      HasCompactSupport (fun y ↦ (χ a y * s.prod (fun b ↦ (1 - χ b y))) • φ y) ∧
      tsupport (fun y ↦ (χ a y * s.prod (fun b ↦ (1 - χ b y))) • φ y) ⊆
        insertCoordinateMap (i a.1) '' interior (C a.1 ×ˢ T a.1) := by
  let ρs : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun y ↦
    s.prod (fun b ↦ (1 - χ b y))
  let ψas : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := fun y ↦
    (χ a y * ρs y) • φ y
  have hρs_cont : ContDiff ℝ 1 ρs := by
    -- The finite product of the complementary cutoffs is still `C¹`.
    simpa [ρs] using
      (contDiff_prod (t := s) (f := fun b y ↦ 1 - χ b y) fun b hb ↦
        contDiff_const.sub (hχ_cont b))
  have hcoeff_cont : ContDiff ℝ 1 (fun y ↦ χ a y * ρs y) := by
    -- Multiplying by the old remainder does not lose regularity.
    simpa [ρs] using (hχ_cont a).mul hρs_cont
  have hcoeff_compact : HasCompactSupport (fun y ↦ χ a y * ρs y) := by
    -- The new coefficient is still supported where the cutoff `χ a` is supported.
    exact (hχ_compact a).mul_right
  refine ⟨?_, ?_, ?_⟩
  · -- Multiply the ambient field by the scalar coefficient in one step.
    change ContDiff ℝ 1 (((fun y ↦ χ a y * s.prod (fun b ↦ (1 - χ b y))) ) • φ)
    simpa [ρs] using hcoeff_cont.smul hφ_cont
  · -- Compact support of the coefficient propagates to the weighted vector field.
    change HasCompactSupport (((fun y ↦ χ a y * s.prod (fun b ↦ (1 - χ b y))) ) • φ)
    simpa [ρs] using hcoeff_compact.smul_right (f' := φ)
  · -- The weighted field cannot leave the chart box already controlling `χ a`.
    exact (tsupport_smul_subset_left (fun y ↦ χ a y * ρs y) φ).trans <|
      (tsupport_mul_subset_left : tsupport (fun y ↦ χ a y * ρs y) ⊆ tsupport (χ a)).trans
        (hχ_subset a)

/-- Helper for Example 8.12: after pulling a compact support back through one
fixed-coordinate chart and flattening the graph by `(z, τ) ↦ (z, σ * (τ - ψ z))`,
the resulting compact set lies in the interior of a centered product box whose
vertical interval crosses `0`. -/
lemma flattenedSupport_hasHalfBox
    {n : ℕ}
    (i : Fin (n + 1))
    {σ : ℝ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hψ_cont : ContDiffOn ℝ 1 ψ C)
    (hφ_compact : HasCompactSupport φ)
    (hφ_subset :
      tsupport φ ⊆ insertCoordinateMap i '' interior (C ×ˢ T)) :
    ∃ R : ℝ, 0 < R ∧
      ((fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦ (p.1, σ * (p.2 - ψ p.1))) ''
          (removeCoordinateMap i '' tsupport φ)) ⊆
        interior ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ Set.Icc (-R) R) := by
  let K : Set (EuclideanSpace ℝ (Fin n) × ℝ) := removeCoordinateMap i '' tsupport φ
  let flatten : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ := fun p ↦
    (p.1, σ * (p.2 - ψ p.1))
  have hK_compact : IsCompact K := by
    -- Pull the compact topological support back through the linear chart inverse.
    simpa [K] using hφ_compact.isCompact.image (removeCoordinateMap i).continuous
  have hK_subset : K ⊆ interior (C ×ˢ T) := by
    -- Every pulled-back support point still lies in the chart interior controlling `φ`.
    intro p hp
    rcases hp with ⟨x, hx, rfl⟩
    rcases hφ_subset hx with ⟨q, hq, hqx⟩
    have hq_eq : q = removeCoordinateMap i x := by
      rw [← hqx, removeCoordinateMap_insertCoordinateMap]
    simpa [hq_eq] using hq
  have hflatten_contOn : ContinuousOn flatten (interior (C ×ˢ T)) := by
    have hψ_pull :
        ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦ ψ p.1) (interior (C ×ˢ T)) := by
      have hψ_on_fst :
          ContinuousOn ψ (Prod.fst '' interior (C ×ˢ T)) := by
        refine hψ_cont.continuousOn.mono ?_
        intro z hz
        rcases hz with ⟨p, hp, rfl⟩
        exact (interior_subset hp).1
      change ContinuousOn (ψ ∘ Prod.fst) (interior (C ×ˢ T))
      exact hψ_on_fst.image_comp_continuous (s := interior (C ×ˢ T)) continuous_fst
    have hsnd :
        ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦ p.2) (interior (C ×ˢ T)) :=
      continuous_snd.continuousOn
    -- The flattening map is continuous on the whole chart interior.
    exact continuous_fst.continuousOn.prodMk ((hsnd.sub hψ_pull).const_mul σ)
  have hflat_compact : IsCompact (flatten '' K) := by
    -- The flattened support remains compact because the flattening is continuous on the chart box.
    exact hK_compact.image_of_continuousOn (hflatten_contOn.mono hK_subset)
  obtain ⟨R₀, hflat_ball₀⟩ :=
    hflat_compact.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin n) × ℝ)
  let R : ℝ := max R₀ 1
  have hR_pos : 0 < R := by
    -- Enlarge the bounding radius so the product box has nonempty interior in every direction.
    dsimp [R]
    positivity
  refine ⟨R, hR_pos, ?_⟩
  intro q hq
  have hq_ball : q ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × ℝ) R := by
    exact Metric.ball_subset_ball (le_max_left _ _) (hflat_ball₀ hq)
  have hq_norm : ‖q‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq_ball
  have hq_max : max ‖q.1‖ ‖q.2‖ < R := by
    simpa [Prod.norm_def] using hq_norm
  have hq_fst_ball : q.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    have hq_fst_norm : ‖q.1‖ < R := lt_of_le_of_lt (le_max_left _ _) hq_max
    simpa [Metric.mem_ball, dist_eq_norm] using hq_fst_norm
  have hq_snd_mem : q.2 ∈ interior (Set.Icc (-R) R) := by
    have hq_snd_norm : ‖q.2‖ < R := lt_of_le_of_lt (le_max_right _ _) hq_max
    have hq_snd_abs : |q.2| < R := by
      simpa [Real.norm_eq_abs] using hq_snd_norm
    rw [interior_Icc, Set.mem_Ioo]
    exact abs_lt.mp hq_snd_abs
  -- Convert the norm bound into the product-box interior needed by the later box divergence step.
  rw [interior_prod_eq]
  exact ⟨Metric.ball_subset_interior_closedBall hq_fst_ball, hq_snd_mem⟩

/-- Helper for Example 8.12: a point on the side boundary or bottom face of the
lower half-box cannot lie in the interior of the centered product box coming
from `flattenedSupport_hasHalfBox`. -/
lemma notMem_interior_centeredBox_of_sideOrBottom
    {n : ℕ}
    {R : ℝ}
    {q : EuclideanSpace ℝ (Fin n) × ℝ}
    (hq_mem :
      q ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ Set.Icc (-R) 0)
    (hq_boundary :
      q.1 ∉ interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ∨ q.2 = -R) :
    q ∉ interior ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ Set.Icc (-R) R) := by
  intro hq_int
  rw [interior_prod_eq, Set.mem_prod] at hq_int
  rcases hq_boundary with hside | hbottom
  · -- A side-face point fails the horizontal interior condition.
    exact hside hq_int.1
  · -- A bottom-face point fails the vertical interior condition.
    rw [interior_Icc, Set.mem_Ioo] at hq_int
    have : (-R : ℝ) < -R := by simpa [hbottom] using hq_int.2.1
    exact lt_irrefl _ this

/-- Helper for Example 8.12: once the flattened support is known to lie in the
interior of the centered product box, the future flattened chart field already
vanishes pointwise on every side face and on the bottom face of the lower
half-box. -/
lemma flattenedChartField_eq_zero_of_sideOrBottom
    {n : ℕ}
    (i : Fin (n + 1))
    {σ : ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hσ_cases : σ = 1 ∨ σ = -1)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {R : ℝ}
    (hflat_subset :
      ((fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦ (p.1, σ * (p.2 - ψ p.1))) ''
          (removeCoordinateMap i '' tsupport φ)) ⊆
        interior ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ Set.Icc (-R) R))
    {q : EuclideanSpace ℝ (Fin n) × ℝ}
    (hq_mem :
      q ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ Set.Icc (-R) 0)
    (hq_boundary :
      q.1 ∉ interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ∨ q.2 = -R) :
    let x := insertCoordinateMap i (q.1, ψ q.1 + σ * q.2)
    ((removeCoordinateMap i (φ x)).1,
      σ * ((φ x) i -
        ∑ j : Fin n, (φ x) (i.succAbove j) *
          fderiv ℝ ψ q.1 (EuclideanSpace.single j (1 : ℝ)))) = 0 := by
  let x : EuclideanSpace ℝ (Fin (n + 1)) := insertCoordinateMap i (q.1, ψ q.1 + σ * q.2)
  have hq_not_int :
      q ∉ interior ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ Set.Icc (-R) R) :=
    notMem_interior_centeredBox_of_sideOrBottom hq_mem hq_boundary
  have hσσ : σ * σ = 1 := by
    rcases hσ_cases with hσ | hσ
    · simp [hσ]
    · simp [hσ]
  have hx_not_mem : x ∉ tsupport φ := by
    intro hx_mem
    have hq_image :
        q ∈
          ((fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦ (p.1, σ * (p.2 - ψ p.1))) ''
            (removeCoordinateMap i '' tsupport φ)) := by
      refine ⟨removeCoordinateMap i x, ⟨x, hx_mem, rfl⟩, ?_⟩
      -- Evaluate the flattening map on the inverse-chart point once and use `σ² = 1`.
      change
        ((removeCoordinateMap i x).1,
          σ * ((removeCoordinateMap i x).2 - ψ ((removeCoordinateMap i x).1))) = q
      rw [show removeCoordinateMap i x = (q.1, ψ q.1 + σ * q.2) by
            simpa [x] using
              (removeCoordinateMap_insertCoordinateMap i (q.1, ψ q.1 + σ * q.2))]
      ext
      · simp
      · rw [show σ * ((ψ q.1 + σ * q.2) - ψ q.1) = (σ * σ) * q.2 by ring]
        simp [hσσ]
    exact hq_not_int (hflat_subset hq_image)
  have hx_zero : φ x = 0 := image_eq_zero_of_notMem_tsupport hx_not_mem
  -- Once the ambient field is zero at the inverse-chart point, every component of the
  -- flattened chart field vanishes.
  ext
  · simp [x, hx_zero]
  · simp [x, hx_zero]

/-- Helper for Example 8.12: on the top face `s = 0`, the flattened chart field
already vanishes whenever the base point lies outside the chart-base interior
that controls the support of the ambient field. -/
lemma flattenedChartField_eq_zero_of_top_outside_baseInterior
    {n : ℕ}
    (i : Fin (n + 1))
    {σ : ℝ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {T : Set ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hφ_subset : tsupport φ ⊆ insertCoordinateMap i '' interior (C ×ˢ T))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∉ interior C) :
    let x := insertCoordinateMap i (z, ψ z)
    ((removeCoordinateMap i (φ x)).1,
      σ * ((φ x) i -
        ∑ j : Fin n, (φ x) (i.succAbove j) *
          fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ)))) = 0 := by
  let x : EuclideanSpace ℝ (Fin (n + 1)) := insertCoordinateMap i (z, ψ z)
  have hx_not_mem : x ∉ tsupport φ := by
    intro hx_mem
    rcases hφ_subset hx_mem with ⟨p, hp, hp_eq⟩
    have hp_prod : p ∈ interior C ×ˢ interior T := by
      simpa [interior_prod_eq] using hp
    have hp_eq' : p = (z, ψ z) := by
      have hremoved := congrArg (removeCoordinateMap i) hp_eq
      simpa [x, removeCoordinateMap_insertCoordinateMap] using hremoved
    have hz_mem : z ∈ interior C := by
      simpa [hp_eq'] using hp_prod.1
    exact hz hz_mem
  have hx_zero : φ x = 0 := by
    -- Outside the topological support the ambient field vanishes pointwise.
    exact image_eq_zero_of_notMem_tsupport hx_not_mem
  -- The top-face flattened field is just the explicit chart formula evaluated at this zero ambient value.
  ext
  · simp [x, hx_zero]
  · simp [x, hx_zero]

/-- Helper for Example 8.12: on a regular neighborhood where the defining
function gradient never vanishes, the divergence integral equals the outward
normal flux across `frontier E`. -/
theorem regularNeighborhoodFlux_eq_boundary
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU_open : IsOpen U)
    (hU_subset : U ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hU_grad : ∀ x ∈ U, gradient h_boundary.boundary.definingFunction x ≠ 0)
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hφ_cont : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_subsetU : tsupport φ ⊆ U) :
    ∫ x in E,
        (∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(domainMeasure Ω) =
      ∫ x in frontier E,
        inner ℝ (φ x) (h_boundary.outwardNormal x)
          ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
  let K : Set (EuclideanSpace ℝ (Fin (n + 1))) := frontier E ∩ tsupport φ
  have hK_compact : IsCompact K := by
    -- The relevant boundary support is compact because `φ` is compactly supported.
    simpa [K, Set.inter_comm] using hφ_compact.isCompact.inter_right isClosed_frontier
  have hK_subset : K ⊆ frontier E := by
    intro x hx
    exact hx.1
  by_cases hK_empty : K = ∅
  · have hφ_frontier_disjoint : tsupport φ ∩ frontier E = ∅ := by
      -- If the frontier-support core is empty, the whole support avoids `frontier E`.
      simpa [K, Set.inter_comm] using hK_empty
    have hboundary_zero :
        ∫ x in frontier E,
          inner ℝ (φ x) (h_boundary.outwardNormal x)
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) = 0 := by
      -- The boundary integrand vanishes pointwise because `φ` is zero on the frontier.
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero ?_
      intro x hx
      have hx_not_mem : x ∉ tsupport φ := by
        intro hx_mem
        have hxK : x ∈ K := ⟨hx, hx_mem⟩
        simpa [hK_empty] using hxK
      simp [image_eq_zero_of_notMem_tsupport hx_not_mem]
    -- Route correction: close the support-disjoint branch directly before reopening any chartwise
    -- localization or implicit-function transport.
    rw [offFrontierDivergence_eq_zero h_boundary φ hφ_cont hφ_compact
      (hφ_subsetU.trans hU_subset) hφ_frontier_disjoint, hboundary_zero]
  obtain ⟨V, hV_open, hV_subsetΩ, hK_cover, hV_grad⟩ :=
    h_boundary.existsFiniteCoordinateGradientCoverOnCompact hK_compact hK_subset
  have hlocalBox :
      ∀ x : K,
        ∃ i : Fin (n + 1),
          ∃ σ : ℝ,
          ∃ C : Set (EuclideanSpace ℝ (Fin n)),
          ∃ T : Set ℝ,
          ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
            (σ = 1 ∨ σ = -1) ∧
            IsCompact C ∧
            Convex ℝ C ∧
            IsCompact T ∧
            Convex ℝ T ∧
            ContDiffOn ℝ 1 ψ C ∧
            (∀ z ∈ C, ψ z ∈ T) ∧
            removeCoordinateMap i (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ interior (C ×ˢ T) ∧
            insertCoordinateMap i '' (C ×ˢ T) ⊆ V i ∧
            (∀ p ∈ C ×ˢ T,
              h_boundary.boundary.definingFunction (insertCoordinateMap i p) = 0 ↔
                ψ p.1 = p.2) ∧
            ∀ p ∈ C ×ˢ T,
              0 < σ * gradient h_boundary.boundary.definingFunction (insertCoordinateMap i p) i := by
    intro x
    rcases Set.mem_iUnion.mp (hK_cover x.2) with ⟨i, hxi⟩
    obtain ⟨σ, C, T, ψ, hσ_cases, hC_compact, hC_convex, hT_compact, hT_convex, hψ_cont,
      hψ_memT, hxBox, hbox_subset, hzero_graph, hsign⟩ :=
      fixedCoordinateSignedGraphBox h_boundary i (hV_open i) (hV_subsetΩ i)
        (fun y hy ↦ hV_grad i y hy) ⟨hK_subset x.2, hxi⟩
    refine ⟨i, σ, C, T, ψ, hσ_cases, hC_compact, hC_convex, hT_compact, hT_convex,
      hψ_cont, hψ_memT, hxBox, hbox_subset, hzero_graph, hsign⟩
  classical
  choose i σ C T ψ hσ_cases hC_compact hC_convex hT_compact hT_convex hψ_cont hψ_memT
    hxBox hbox_subset hzero_graph hsign using hlocalBox
  have hchartOpen :
      ∀ x : K,
        IsOpen (insertCoordinateMap (i x) '' interior (C x ×ˢ T x)) := by
    intro x
    obtain ⟨e, he⟩ := insertCoordinateMap_isInvertible (i x)
    have he_fun :
        ∀ p : EuclideanSpace ℝ (Fin n) × ℝ,
          e p = insertCoordinateMap (i x) p := by
      intro p
      simpa using congrArg
        (fun m : EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ]
            EuclideanSpace ℝ (Fin (n + 1)) ↦
          m p) he
    have himage :
        insertCoordinateMap (i x) '' interior (C x ×ˢ T x) =
          e '' interior (C x ×ˢ T x) := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, by simpa using he_fun p⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, by simpa using (he_fun p).symm⟩
    rw [himage]
    -- The fixed-coordinate chart is a linear equivalence, so it carries open product boxes to open sets.
    exact e.isOpenMap _ isOpen_interior
  have hchartCover :
      K ⊆ ⋃ x : K, insertCoordinateMap (i x) '' interior (C x ×ˢ T x) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    refine ⟨removeCoordinateMap (i ⟨x, hx⟩) x, hxBox ⟨x, hx⟩, ?_⟩
    simpa using insertCoordinateMap_removeCoordinateMap (i ⟨x, hx⟩) x
  obtain ⟨t, ht_cover⟩ :=
    hK_compact.elim_finite_subcover
      (fun x : K ↦ insertCoordinateMap (i x) '' interior (C x ×ˢ T x))
      hchartOpen hchartCover
  obtain ⟨Vshr, hVshr_open, hVshr_cover, hVshr_compact, hVshr_subset, χ, hχ_cont,
      hχ_compact, hχ_subset, hχ_one, hχ_range⟩ :=
    finiteCoordinateBoxShrunkCutoffs h_boundary hU_open hU_subset hU_grad φ hφ_cont
      hφ_compact hφ_subsetU K rfl hK_compact hK_subset
      hσ_cases hC_compact hC_convex hT_compact hT_convex hψ_cont hψ_memT
      hxBox (fun x ↦ (hbox_subset x).trans (hV_subsetΩ (i x))) hzero_graph hsign ht_cover
  let ρ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun y ↦
    t.attach.prod (fun a ↦ (1 - χ a y))
  let φFar : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ρ • φ
  let φNear : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    (fun y ↦ 1 - ρ y) • φ
  have hρ_cont : ContDiff ℝ 1 ρ := by
    -- The finite product of the complementary chart cutoffs stays `C¹`.
    simpa [ρ] using
      (contDiff_prod (t := t.attach) (f := fun a y ↦ 1 - χ a y) fun a ha ↦
        contDiff_const.sub (hχ_cont a))
  have hφFar_cont : ContDiff ℝ 1 φFar := by
    -- Multiplying by the cutoff product keeps the far remainder `C¹`.
    simpa [φFar] using hρ_cont.smul hφ_cont
  have hφNear_cont : ContDiff ℝ 1 φNear := by
    -- The complementary near field is also `C¹`.
    simpa [φNear] using (contDiff_const.sub hρ_cont).smul hφ_cont
  have hφFar_compact : HasCompactSupport φFar := by
    -- The far remainder is still compactly supported because it is a scalar multiple of `φ`.
    simpa [φFar] using hφ_compact.smul_left (f := ρ)
  have hφNear_compact : HasCompactSupport φNear := by
    -- The near field inherits compact support from `φ`.
    simpa [φNear] using hφ_compact.smul_left (f := fun y ↦ 1 - ρ y)
  have hφFar_subset :
      tsupport φFar ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The far remainder cannot create support outside the original field support.
    exact (tsupport_smul_subset_right ρ φ).trans (hφ_subsetU.trans hU_subset)
  have hφNear_subset :
      tsupport φNear ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The near field also stays inside the ambient open set.
    exact (tsupport_smul_subset_right (fun y ↦ 1 - ρ y) φ).trans (hφ_subsetU.trans hU_subset)
  have hφFar_frontier_disjoint : tsupport φFar ∩ frontier E = ∅ := by
    -- Route correction: the shrunk cutoff cover makes the product coefficient vanish on a whole
    -- neighborhood of each point of `frontier E ∩ tsupport φ`, so the far remainder is genuinely
    -- support-disjoint from the frontier.
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx_front : x ∈ frontier E := hx.2
    by_cases hxφ : x ∈ tsupport φ
    · have hρ_zero : ρ =ᶠ[nhds x] 0 := by
        exact finiteCoordinateCutoffProduct_eventuallyEq_zero hVshr_open hVshr_cover hχ_one
          ⟨hx_front, hxφ⟩
      have hx_not_mem : x ∉ tsupport φFar := by
        rw [notMem_tsupport_iff_eventuallyEq]
        filter_upwards [hρ_zero] with y hy
        simp [φFar, hy]
      exact hx_not_mem hx.1
    · rw [notMem_tsupport_iff_eventuallyEq] at hxφ
      have hx_not_mem : x ∉ tsupport φFar := by
        rw [notMem_tsupport_iff_eventuallyEq]
        filter_upwards [hxφ] with y hy
        simp [φFar, hy]
      exact hx_not_mem hx.1
  have hsplit : ∀ x, φ x = φFar x + φNear x := by
    -- Split `φ` into the frontier-disjoint remainder and the near piece that still needs
    -- chartwise localization.
    intro x
    simp [φFar, φNear, ρ, sub_eq_add_neg, add_smul]
  have hφFar_diff : Differentiable ℝ φFar := hφFar_cont.differentiable_one
  have hφNear_diff : Differentiable ℝ φNear := hφNear_cont.differentiable_one
  have hdiv_split :
      ∀ x,
        (∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i) =
          (∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i) +
            (∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i) := by
    intro x
    have hfd :
        fderiv ℝ φ x = fderiv ℝ φFar x + fderiv ℝ φNear x := by
      rw [show φ = fun y ↦ φFar y + φNear y by
            funext y
            exact hsplit y]
      exact fderiv_add (hφFar_diff x) (hφNear_diff x)
    -- Rewrite the raw divergence through linearity of the Fréchet derivative.
    simpa [Finset.sum_add_distrib] using
      congrArg
        (fun A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
            EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), A (EuclideanSpace.single i (1 : ℝ)) i)
        hfd
  have hdivFar_integrable :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i)
        (domainMeasure Ω) := by
    -- The far remainder has compact support, so its raw divergence is integrable.
    exact rawDivergenceIntegrable hφFar_cont hφFar_compact
  have hdivNear_integrable :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
        (domainMeasure Ω) := by
    -- The same compact-support integrability applies to the near field.
    exact rawDivergenceIntegrable hφNear_cont hφNear_compact
  have hdivFar_restrict :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i)
        ((domainMeasure Ω).restrict E) :=
    hdivFar_integrable.restrict
  have hdivNear_restrict :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
        ((domainMeasure Ω).restrict E) :=
    hdivNear_integrable.restrict
  have hboundary_eq :
      ∫ x in frontier E,
        inner ℝ (φ x) (h_boundary.outwardNormal x)
          ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) =
      ∫ x in frontier E,
        inner ℝ (φNear x) (h_boundary.outwardNormal x)
          ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
    refine MeasureTheory.setIntegral_congr_fun isClosed_frontier.measurableSet ?_
    intro x hx
    have hφFar_zero : φFar x = 0 := by
      have hx_not_mem : x ∉ tsupport φFar := by
        intro hx_mem
        have hx_inter : x ∈ tsupport φFar ∩ frontier E := ⟨hx_mem, hx⟩
        simpa [hφFar_frontier_disjoint] using hx_inter
      exact image_eq_zero_of_notMem_tsupport hx_not_mem
    -- On the frontier the far remainder vanishes, so only the near piece contributes.
    calc
      inner ℝ (φ x) (h_boundary.outwardNormal x)
        = inner ℝ (φFar x + φNear x) (h_boundary.outwardNormal x) := by
            rw [hsplit x]
      _ = inner ℝ (φNear x) (h_boundary.outwardNormal x) := by
            simp [hφFar_zero]
  have hnear :
      ∫ x in E,
        (∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(domainMeasure Ω) =
      ∫ x in frontier E,
        inner ℝ (φNear x) (h_boundary.outwardNormal x)
          ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
    let μb : MeasureTheory.Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
      MeasureTheory.Measure.euclideanHausdorffMeasure n
    have localizedGraphBoxFlux_eq_boundary :
        ∀ a : {x : K // x ∈ t},
          ∀ ψloc : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
            ContDiff ℝ 1 ψloc →
            HasCompactSupport ψloc →
            tsupport ψloc ⊆
              insertCoordinateMap (i a.1) '' interior (C a.1 ×ˢ T a.1) →
            ∫ x in E,
              (∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i')
              ∂(domainMeasure Ω) =
            ∫ x in frontier E,
              inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb := by
      intro a ψloc hψloc_cont hψloc_compact hψloc_subset
      -- Route correction: the finite-cutoff induction is now explicit, so the only remaining
      -- geometric blocker is this one-chart signed-graph-box flux identity.
      have hbox_subsetΩ :
          insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) ⊆
            (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
        -- The chosen chart box already sits inside the ambient domain `Ω`.
        exact (hbox_subset a.1).trans (hV_subsetΩ (i a.1))
      obtain ⟨R, hR_pos, hflat_subset⟩ :=
        flattenedSupport_hasHalfBox (i := i a.1) (σ := σ a.1)
          (C := C a.1) (T := T a.1) (ψ := ψ a.1) (φ := ψloc)
          (hψ_cont := hψ_cont a.1) hψloc_compact hψloc_subset
      let splitPull : EuclideanSpace ℝ (Fin n) × ℝ →
          EuclideanSpace ℝ (Fin (n + 1)) := fun p ↦
        insertCoordinateMap (i a.1) p
      let chartMap : EuclideanSpace ℝ (Fin n) × ℝ →
          EuclideanSpace ℝ (Fin (n + 1)) := fun q ↦
        insertCoordinateMap (i a.1) (q.1, ψ a.1 q.1 + σ a.1 * q.2)
      let flatField : EuclideanSpace ℝ (Fin n) × ℝ →
          EuclideanSpace ℝ (Fin n) × ℝ := fun q ↦
        let x := chartMap q
        ((removeCoordinateMap (i a.1) (ψloc x)).1,
          σ a.1 * ((ψloc x) (i a.1) -
            ∑ j : Fin n, (ψloc x) ((i a.1).succAbove j) *
              fderiv ℝ (ψ a.1) q.1 (EuclideanSpace.single j (1 : ℝ))))
      let flattenedBox : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ Set.Icc (-R) R
      have hσ_sq : σ a.1 * σ a.1 = 1 := by
        -- The signed chart orientation is normalized once so later `σ²` rewrites stay propositional.
        exact signedChartSign_sq_eq_one (hσ_cases a.1)
      have hflattenedChartField_zero :
          ∀ q : EuclideanSpace ℝ (Fin n) × ℝ,
            q ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ Set.Icc (-R) 0 →
            q.1 ∉ interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ∨ q.2 = -R →
            flatField q = 0 := by
        intro q hq_mem hq_boundary
        -- The support geometry is now packaged: on the side faces and bottom face,
        -- the future flattened chart field is already zero pointwise.
        simpa [flatField, chartMap] using
          flattenedChartField_eq_zero_of_sideOrBottom (i := i a.1)
            (σ := σ a.1) (ψ := ψ a.1) (hσ_cases := hσ_cases a.1)
            (φ := ψloc) (R := R) hflat_subset hq_mem hq_boundary
      have hchartMap_top :
          ∀ z : EuclideanSpace ℝ (Fin n),
            chartMap (z, 0) = insertCoordinateMap (i a.1) (z, ψ a.1 z) := by
        intro z
        -- On the top face `s = 0`, the signed shear collapses back to the graph chart.
        simp [chartMap]
      have hchartMap_top_mem_frontier :
          ∀ z : EuclideanSpace ℝ (Fin n),
            z ∈ C a.1 → chartMap (z, 0) ∈ frontier E := by
        intro z hz
        have hz_box : (z, ψ a.1 z + σ a.1 * (0 : ℝ)) ∈ C a.1 ×ˢ T a.1 := by
          simpa using ⟨hz, hψ_memT a.1 z hz⟩
        -- The new chart-geometry bridge isolates the top face as the frontier slice `s = 0`.
        have hfrontier : chartMap (z, 0) ∈ frontier E := by
          exact
            (memFrontier_insertCoordinateMap_graphShear_iff
              (q := (z, 0))
              (U := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
              h_boundary (i a.1) (fun x hx ↦ hx) (hσ_cases a.1)
              hbox_subsetΩ (hzero_graph a.1) (by simpa using hz_box)).2 (by simp)
        simpa [hchartMap_top z] using hfrontier
      have hflatField_top_commonDensity :
          ∀ {z : EuclideanSpace ℝ (Fin n)},
            z ∈ interior (C a.1) →
              σ a.1 *
                  ‖gradient h_boundary.boundary.definingFunction (chartMap (z, 0))‖ *
                  inner ℝ
                    (ψloc (chartMap (z, 0)))
                    (h_boundary.outwardNormal (chartMap (z, 0))) =
                gradient h_boundary.boundary.definingFunction (chartMap (z, 0)) (i a.1) *
                  (flatField (z, 0)).2 := by
        intro z hz
        -- On the surviving top face, the flattened vertical component is exactly the common chart
        -- density from the boundary-pairing identity.
        have hcommon :
            σ a.1 *
                ‖gradient h_boundary.boundary.definingFunction
                    (insertCoordinateMap (i a.1) (z, ψ a.1 z))‖ *
                inner ℝ
                  (ψloc (insertCoordinateMap (i a.1) (z, ψ a.1 z)))
                  (h_boundary.outwardNormal (insertCoordinateMap (i a.1) (z, ψ a.1 z))) =
              (σ a.1 *
                  gradient h_boundary.boundary.definingFunction
                    (insertCoordinateMap (i a.1) (z, ψ a.1 z)) (i a.1)) *
                ((ψloc (insertCoordinateMap (i a.1) (z, ψ a.1 z))) (i a.1) -
                  ∑ j : Fin n,
                    (ψloc (insertCoordinateMap (i a.1) (z, ψ a.1 z))) ((i a.1).succAbove j) *
                      fderiv ℝ (ψ a.1) z (EuclideanSpace.single j (1 : ℝ))) := by
          simpa using
            (graphBoxBoundaryDensity_mul_norm_eq_commonDensity
              (U := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
              (σ := σ a.1) h_boundary (i a.1) (fun x hx ↦ hx) (hψ_cont a.1) hbox_subsetΩ
              (hψ_memT a.1) (hzero_graph a.1) ψloc hz)
        -- Rewrite the explicit top-face vertical component of `flatField` using `σ² = 1`.
        have htopSecond :
            (flatField (z, 0)).2 =
              σ a.1 *
                ((ψloc (chartMap (z, 0))) (i a.1) -
                  ∑ j : Fin n,
                    (ψloc (chartMap (z, 0))) ((i a.1).succAbove j) *
                      fderiv ℝ (ψ a.1) z (EuclideanSpace.single j (1 : ℝ))) := by
          simp [flatField, chartMap]
        calc
          σ a.1 *
              ‖gradient h_boundary.boundary.definingFunction (chartMap (z, 0))‖ *
              inner ℝ
                (ψloc (chartMap (z, 0)))
                (h_boundary.outwardNormal (chartMap (z, 0)))
              =
            (σ a.1 *
                gradient h_boundary.boundary.definingFunction (chartMap (z, 0)) (i a.1)) *
              ((ψloc (chartMap (z, 0))) (i a.1) -
                ∑ j : Fin n,
                  (ψloc (chartMap (z, 0))) ((i a.1).succAbove j) *
                    fderiv ℝ (ψ a.1) z (EuclideanSpace.single j (1 : ℝ))) := by
              simpa [hchartMap_top z] using hcommon
          _ =
            gradient h_boundary.boundary.definingFunction (chartMap (z, 0)) (i a.1) *
              (flatField (z, 0)).2 := by
              rw [htopSecond]
              ring_nf
      have hflatField_top_zero_outside :
          ∀ {z : EuclideanSpace ℝ (Fin n)},
            z ∉ interior (C a.1) → flatField (z, 0) = 0 := by
        intro z hz
        -- The chart-supported ambient field cannot contribute on the top face away from the
        -- graph patch base, so the flattened field vanishes there before any integration step.
        simpa [flatField, chartMap] using
          flattenedChartField_eq_zero_of_top_outside_baseInterior
            (i := i a.1) (σ := σ a.1) (C := C a.1) (T := T a.1)
            (ψ := ψ a.1) (φ := ψloc) hψloc_subset hz
      let lowerHalfBox : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ Set.Icc (-R) 0
      let topFaceIntegral : ℝ :=
        ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, (flatField (z, 0)).2
      have hsplitPull_cont : Continuous splitPull := by
        -- The fixed-coordinate insertion chart is linear, hence continuous.
        simpa [splitPull] using (insertCoordinateMap (i a.1)).continuous
      have hflattenedBox_openInterior : IsOpen (interior flattenedBox) := isOpen_interior
      have hlowerHalfImage :
          ∀ {x : EuclideanSpace ℝ (Fin (n + 1))},
            x ∈ chartMap ''
                {q : EuclideanSpace ℝ (Fin n) × ℝ |
                  (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 ∧ q.2 ≤ 0} ↔
              x ∈ insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) ∩ E := by
        intro x
        -- Normalize the lower-half image once before the later change-of-variables step.
        simpa [chartMap] using
          (memImage_insertCoordinateMap_graphShear_lowerHalf_iff
            (U := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
            h_boundary (i a.1) (fun x hx ↦ hx) (hσ_cases a.1) (hT_convex a.1)
            hbox_subsetΩ (hψ_memT a.1) (hzero_graph a.1) (hsign a.1)
            (x := x))
      have htopFaceImage :
          ∀ {x : EuclideanSpace ℝ (Fin (n + 1))},
            x ∈ chartMap ''
                {q : EuclideanSpace ℝ (Fin n) × ℝ |
                  (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 ∧ q.2 = 0} ↔
              x ∈ insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) ∩ frontier E := by
        intro x
        -- The same normalization isolates the top face as the graph-frontier slice.
        simpa [chartMap] using
          (memImage_insertCoordinateMap_graphShear_topFace_iff
            (U := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
            h_boundary (i a.1) (fun x hx ↦ hx) (hσ_cases a.1)
            hbox_subsetΩ (hzero_graph a.1) (x := x))
      have hchartMap_injective : Function.Injective chartMap := by
        -- The signed graph shear stays injective in the chosen chart coordinates.
        simpa [chartMap] using
          (insertCoordinateMap_graphShear_injective
            (i := i a.1) (hσ_cases := hσ_cases a.1) (ψ := ψ a.1))
      have hchartMap_memE_iff :
          ∀ {q : EuclideanSpace ℝ (Fin n) × ℝ},
            (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 →
              (chartMap q ∈ E ↔ q.2 ≤ 0) := by
        intro q hq
        -- Record the pointwise membership bridge before the transport step opens the image integral.
        simpa [chartMap] using
          (memE_insertCoordinateMap_graphShear_iff
            (U := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
            h_boundary (i a.1) (fun x hx ↦ hx) (hσ_cases a.1) (hT_convex a.1)
            hbox_subsetΩ (hψ_memT a.1) (hzero_graph a.1) (hsign a.1) hq)
      have hchartMap_memFrontier_iff :
          ∀ {q : EuclideanSpace ℝ (Fin n) × ℝ},
            (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 →
              (chartMap q ∈ frontier E ↔ q.2 = 0) := by
        intro q hq
        -- The frontier slice of the chart is exactly the top face `q.2 = 0`.
        simpa [chartMap] using
          (memFrontier_insertCoordinateMap_graphShear_iff
            (U := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
            h_boundary (i a.1) (fun x hx ↦ hx) (hσ_cases a.1)
            hbox_subsetΩ (hzero_graph a.1) hq)
      have hflattenedChartField_second_zero :
          ∀ q : EuclideanSpace ℝ (Fin n) × ℝ,
            q ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ Set.Icc (-R) 0 →
            q.1 ∉ interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ∨ q.2 = -R →
            (flatField q).2 = 0 := by
        intro q hq_mem hq_boundary
        -- Keep only the surviving scalar face-vanishing fact needed by the box divergence route.
        exact congrArg Prod.snd (hflattenedChartField_zero q hq_mem hq_boundary)
      have hflatField_topSecond_zero_outside :
          ∀ {z : EuclideanSpace ℝ (Fin n)},
            z ∉ interior (C a.1) → (flatField (z, 0)).2 = 0 := by
        intro z hz
        -- Off the chart base, the top-face scalar density already vanishes before transport.
        exact congrArg Prod.snd (hflatField_top_zero_outside hz)
      have hflatField_topSecond_zero_outsideBall :
          ∀ {z : EuclideanSpace ℝ (Fin n)},
            z ∉ interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) →
              (flatField (z, 0)).2 = 0 := by
        intro z hz
        let x : EuclideanSpace ℝ (Fin (n + 1)) := chartMap (z, 0)
        have hx_not_mem : x ∉ tsupport ψloc := by
          intro hx_mem
          have hflat_mem :
              (z, 0) ∈
                ((fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦
                    (p.1, σ a.1 * (p.2 - ψ a.1 p.1))) ''
                  (removeCoordinateMap (i a.1) '' tsupport ψloc)) := by
            refine ⟨removeCoordinateMap (i a.1) x, ⟨x, hx_mem, rfl⟩, ?_⟩
            -- Evaluate the flattening map on the inverse-chart point of the top face.
            change
              (((removeCoordinateMap (i a.1) x).1,
                  σ a.1 *
                    ((removeCoordinateMap (i a.1) x).2 -
                      ψ a.1 ((removeCoordinateMap (i a.1) x).1))) :
                EuclideanSpace ℝ (Fin n) × ℝ) = (z, 0)
            rw [show removeCoordinateMap (i a.1) x = (z, ψ a.1 z) by
                  simpa [x, chartMap] using
                    (removeCoordinateMap_insertCoordinateMap (i a.1)
                      (z, ψ a.1 z))]
            ring
          have hinside := hflat_subset hflat_mem
          rw [interior_prod_eq, Set.mem_prod] at hinside
          exact hz hinside.1
        have hx_zero : ψloc x = 0 := image_eq_zero_of_notMem_tsupport hx_not_mem
        -- Once the ambient field vanishes, the surviving scalar top-face component is also zero.
        have hx_coord_zero :
            ∀ j : Fin (n + 1), (ψloc x) j = 0 := by
          intro j
          simpa using congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) ↦ v j) hx_zero
        have hsum_zero :
            ∑ j,
                (ψloc x).ofLp ((i a.1).succAbove j) *
                  (fderiv ℝ (ψ a.1) z) (EuclideanSpace.single j 1) = 0 := by
          simp [hx_coord_zero]
        calc
          (flatField (z, 0)).2
              = σ a.1 *
                  ((ψloc x).ofLp (i a.1) -
                    ∑ j,
                      (ψloc x).ofLp ((i a.1).succAbove j) *
                        (fderiv ℝ (ψ a.1) z) (EuclideanSpace.single j 1)) := by
                  simp [flatField, x, chartMap]
          _ = σ a.1 * (0 - 0) := by rw [hx_coord_zero, hsum_zero]
          _ = 0 := by ring
      have hchartIntegral_eq_topFaceIntegral :
          ∫ x in E,
            (∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i')
            ∂(domainMeasure Ω) =
              topFaceIntegral := by
        have hE_null : MeasureTheory.NullMeasurableSet E (domainMeasure Ω) := by
          have hdef_ae :
              MeasureTheory.AEStronglyMeasurable
                h_boundary.boundary.definingFunction (domainMeasure Ω) := by
            simpa [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using
              h_boundary.boundary.contDiffOn_definingFunction.continuousOn.aestronglyMeasurable
                (μ := (MeasureTheory.MeasureSpace.volume :
                  MeasureTheory.Measure (EuclideanSpace ℝ (Fin (n + 1)))))
                Ω.2.measurableSet
          -- The defining-function sublevel description makes `E` null-measurable for the
          -- restricted ambient measure used by the divergence pairing.
          rw [h_boundary.boundary.interior_eq_nonpos]
          exact Ω.2.measurableSet.nullMeasurableSet.inter
            (hdef_ae.nullMeasurableSet_le MeasureTheory.aestronglyMeasurable_const)
        have hchartIntegral_eq_chartImage :
            ∫ x in E,
              (∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i')
              ∂(domainMeasure Ω) =
            ∫ x in chartMap ''
                {q : EuclideanSpace ℝ (Fin n) × ℝ |
                  (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 ∧ q.2 ≤ 0},
              (∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i')
                ∂(domainMeasure Ω) := by
          have hchartIntegral_eq_boxImage :
              ∫ x in E,
                (∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i')
                ∂(domainMeasure Ω) =
              ∫ x in insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) ∩ E,
                (∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i')
                  ∂(domainMeasure Ω) := by
            refine MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hE_null ?_ ?_
            · intro x hx
              exact hx.2
            · filter_upwards with x hx
              have hx_not_mem :
                  x ∉ insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) := by
                intro hx_mem
                exact hx.2 ⟨hx_mem, hx.1⟩
              have hx_not_tsupport : x ∉ tsupport ψloc := by
                intro hx_support
                rcases hψloc_subset hx_support with ⟨p, hp, rfl⟩
                exact ⟨p, interior_subset hp, rfl⟩ |> hx_not_mem
              -- Outside the chart box, the ambient field vanishes, so its raw divergence vanishes too.
              exact rawDivergence_eq_zero_of_notMem_tsupport (φ := ψloc) hx_not_tsupport
          have hboxImage_eq_chartImage :
              insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) ∩ E =
                chartMap ''
                  {q : EuclideanSpace ℝ (Fin n) × ℝ |
                    (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 ∧ q.2 ≤ 0} := by
            ext x
            exact (hlowerHalfImage (x := x)).symm
          -- The support localization is now complete; only the change of variables through
          -- `chartMap` and the lower-half-box divergence theorem remain.
          calc
            ∫ x in E,
                (∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i')
                ∂(domainMeasure Ω)
              =
                ∫ x in insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) ∩ E,
                  (∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i')
                  ∂(domainMeasure Ω) := hchartIntegral_eq_boxImage
            _ =
                ∫ x in chartMap ''
                    {q : EuclideanSpace ℝ (Fin n) × ℝ |
                      (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 ∧ q.2 ≤ 0},
                  (∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i')
                    ∂(domainMeasure Ω) := by
                  rw [hboxImage_eq_chartImage]
        -- TODO: only two ambient steps remain.
        -- First, transport the localized chart-image integral through the injective `chartMap`
        -- to the lower-half source; then use the face-vanishing scalar lemma
        -- `hflattenedChartField_second_zero` to collapse the resulting box divergence identity
        -- to `topFaceIntegral`.
        let _unusedLowerHalfBox := lowerHalfBox
        let shear : EuclideanSpace ℝ (Fin n) × ℝ →
            EuclideanSpace ℝ (Fin n) × ℝ := fun q ↦
          (q.1, ψ a.1 q.1 + σ a.1 * q.2)
        let lowerSource : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
          {q | shear q ∈ C a.1 ×ˢ T a.1 ∧ q.2 ≤ 0}
        have hshear_injective : Function.Injective shear := by
          -- Record the pure product-coordinate shear injectivity once before the same-type
          -- change-of-variables step.
          simpa [shear] using graphShear_injective (hσ_cases a.1) (ψ a.1)
        let rawDiv : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x ↦
          ∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i'
        have hchartMap_eq_splitPull_shear :
            chartMap = fun q ↦ splitPull (shear q) := by
          -- Factor the nonlinear chart map into the fixed linear insertion and the same-type shear.
          funext q
          simp [chartMap, splitPull, shear]
        have hchartImage_eq_splitPull :
            chartMap '' lowerSource = splitPull '' (shear '' lowerSource) := by
          -- Normalize the chart image to the split coordinates before any change of variables.
          simpa [hchartMap_eq_splitPull_shear, Function.comp, lowerSource, shear] using
            (Set.image_image splitPull shear lowerSource).symm
        obtain ⟨eSplit, heSplit⟩ := insertCoordinateMap_isInvertible (i a.1)
        have hsplitPull_eq :
            (eSplit : EuclideanSpace ℝ (Fin n) × ℝ →
              EuclideanSpace ℝ (Fin (n + 1))) = splitPull := by
          funext q
          simpa [splitPull] using
            congrArg
              (fun m : EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ]
                  EuclideanSpace ℝ (Fin (n + 1)) ↦
                m q) heSplit
        have hsplitPull_emb : MeasurableEmbedding splitPull := by
          -- The fixed-coordinate insertion is a measurable embedding via its continuous inverse.
          simpa [hsplitPull_eq] using eSplit.toHomeomorph.measurableEmbedding
        have hchartImage_subsetΩ :
            chartMap '' lowerSource ⊆
              (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
          intro x hx
          rcases hx with ⟨q, hq, rfl⟩
          exact hbox_subsetΩ ⟨shear q, hq.1, by simp [splitPull, hchartMap_eq_splitPull_shear]⟩
        have htransportToShear :
            ∫ x in chartMap '' lowerSource, rawDiv x ∂(domainMeasure Ω) =
              ∫ q in shear '' lowerSource, rawDiv (splitPull q) ∂MeasureTheory.volume := by
          -- Route correction: strip off the fixed linear insertion once, before handling the
          -- genuine same-type Jacobian computation for the shear.
          rw [hchartImage_eq_splitPull, domainMeasure_def,
            EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
          change
            ∫ x, rawDiv x
              ∂((MeasureTheory.volume.restrict
                    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))).restrict
                  (splitPull '' (shear '' lowerSource))) =
              ∫ q in shear '' lowerSource, rawDiv (splitPull q) ∂MeasureTheory.volume
          rw [MeasureTheory.Measure.restrict_restrict_of_subset]
          · change
              ∫ x in splitPull '' (shear '' lowerSource), rawDiv x ∂MeasureTheory.volume =
                ∫ q in shear '' lowerSource, rawDiv (splitPull q) ∂MeasureTheory.volume
            exact
              (insertCoordinateMap_measurePreserving (i a.1)).setIntegral_image_emb
                hsplitPull_emb rawDiv (shear '' lowerSource)
          · simpa [hchartImage_eq_splitPull] using hchartImage_subsetΩ
        -- TODO: the remaining ambient bridge is now isolated to two explicit statements.
        -- First transport the shear-image integral back to `lowerSource` by a same-type
        -- change-of-variables formula for `shear` on the measurable source set `lowerSource`.
        -- Then rewrite the transported density as the raw divergence of `flatField` and collapse
        -- the lower-half-box divergence to the top face.
        have hshearImageIntegral_eq_lowerSourceIntegral :
            ∫ q in shear '' lowerSource, rawDiv (splitPull q) ∂MeasureTheory.volume =
              ∫ q in lowerSource, rawDiv (chartMap q) ∂MeasureTheory.volume := by
          have hC_meas : MeasurableSet (C a.1) := (hC_compact a.1).measurableSet
          let ψbase : C a.1 → ℝ := fun z ↦ ψ a.1 z
          have hψbase_meas : Measurable ψbase := by
            -- Restrict the chart graph to the compact base before extending it measurably.
            simpa [ψbase] using
              (continuousOn_iff_continuous_restrict.mp (hψ_cont a.1).continuousOn).measurable
          obtain ⟨ψext, hψext_meas, hψext_comp⟩ :=
            (MeasurableEmbedding.subtype_coe hC_meas).exists_measurable_extend hψbase_meas
              (fun _ ↦ ⟨(0 : ℝ)⟩)
          let shearExt : EuclideanSpace ℝ (Fin n) × ℝ →
              EuclideanSpace ℝ (Fin n) × ℝ := fun q ↦
            (q.1, ψext q.1 + σ a.1 * q.2)
          have hψext_eq :
              ∀ z ∈ C a.1, ψext z = ψ a.1 z := by
            intro z hz
            have hcomp := congrFun hψext_comp ⟨z, hz⟩
            simpa [ψbase] using hcomp
          have hshearExt_meas : Measurable shearExt := by
            -- The measurable extension lets the product-coordinate shear exist on the whole space.
            refine measurable_fst.prod_mk ?_
            exact hψext_meas.comp measurable_fst |>.add
              ((measurable_const.mul measurable_snd))
          have hshearExt_pres :
              MeasureTheory.MeasurePreserving shearExt MeasureTheory.volume MeasureTheory.volume := by
            rcases hσ_cases a.1 with hσ | hσ
            · -- When `σ = 1`, the shear is a measurable skew product of translations.
              subst hσ
              simpa [shearExt] using
                (MeasureTheory.MeasurePreserving.id MeasureTheory.volume).skew_product
                  (hψext_meas.comp measurable_fst).add measurable_snd
                  (Filter.Eventually.of_forall fun z ↦
                    (measurePreserving_add_right MeasureTheory.volume (ψext z)).map_eq)
            · -- When `σ = -1`, compose negation with the translated fiber map.
              subst hσ
              refine
                (MeasureTheory.MeasurePreserving.id MeasureTheory.volume).skew_product
                  ((hψext_meas.comp measurable_fst).sub measurable_snd) ?_
              refine Filter.Eventually.of_forall ?_
              intro z
              calc
                Measure.map (fun s : ℝ ↦ ψext z - s) MeasureTheory.volume
                    = Measure.map (fun t : ℝ ↦ t + ψext z)
                        (Measure.map (fun s : ℝ ↦ -s) MeasureTheory.volume) := by
                          rw [Measure.map_map measurable_neg (measurable_id.add measurable_const)]
                          rfl
                _ = Measure.map (fun t : ℝ ↦ t + ψext z) MeasureTheory.volume := by
                      rw [Measure.map_neg_eq_self]
                _ = MeasureTheory.volume := by
                      simpa using
                        (measurePreserving_add_right MeasureTheory.volume (ψext z)).map_eq
          have hshearExt_bijective : Function.Bijective shearExt := by
            refine ⟨?_, ?_⟩
            · -- The signed graph shear is injective for any graph function.
              simpa [shearExt] using graphShear_injective (hσ_cases a.1) ψext
            · intro p
              refine ⟨(p.1, σ a.1 * (p.2 - ψext p.1)), ?_⟩
              rcases hσ_cases a.1 with hσ | hσ <;> simp [shearExt, hσ]
          let shearExtEquiv :
              (EuclideanSpace ℝ (Fin n) × ℝ) ≃ᵐ (EuclideanSpace ℝ (Fin n) × ℝ) where
            toEquiv := Equiv.ofBijective shearExt hshearExt_bijective
            measurable_toFun := hshearExt_meas
            measurable_invFun := by
              have hsymm :
                  (Equiv.ofBijective shearExt hshearExt_bijective).symm =
                    fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦
                      (p.1, σ a.1 * (p.2 - ψext p.1)) := by
                funext p
                apply (hshearExt_bijective.1)
                simpa [shearExt] using
                  (Equiv.ofBijective_apply_symm_apply shearExt hshearExt_bijective p)
              rw [hsymm]
              exact measurable_fst.prod_mk <|
                measurable_const.mul ((measurable_snd).sub (hψext_meas.comp measurable_fst))
          have hshearExt_image_eq :
              shearExt '' lowerSource = shear '' lowerSource := by
            ext p
            constructor
            · rintro ⟨q, hq, rfl⟩
              refine ⟨q, hq, ?_⟩
              have hqC : q.1 ∈ C a.1 := hq.1.1
              simp [shearExt, shear, hψext_eq q.1 hqC]
            · rintro ⟨q, hq, rfl⟩
              refine ⟨q, hq, ?_⟩
              have hqC : q.1 ∈ C a.1 := hq.1.1
              simp [shearExt, shear, hψext_eq q.1 hqC]
          have hsplitPull_shearExt_eq_chartMap :
              ∀ q ∈ lowerSource, splitPull (shearExt q) = chartMap q := by
            intro q hq
            have hqC : q.1 ∈ C a.1 := hq.1.1
            simp [splitPull, shearExt, chartMap, hψext_eq q.1 hqC]
          have hlowerSource_eq :
              lowerSource =
                {q : EuclideanSpace ℝ (Fin n) × ℝ |
                  shearExt q ∈ C a.1 ×ˢ T a.1 ∧ q.2 ≤ 0} := by
            ext q
            constructor
            · intro hq
              have hqC : q.1 ∈ C a.1 := hq.1.1
              simpa [lowerSource, shear, shearExt, hψext_eq q.1 hqC] using hq
            · intro hq
              have hqC : q.1 ∈ C a.1 := hq.1.1
              simpa [lowerSource, shear, shearExt, hψext_eq q.1 hqC] using hq
          have hlowerSource_meas : MeasurableSet lowerSource := by
            -- The lower source is measurable once the chart graph is replaced by the globalized
            -- measurable shear extension.
            rw [hlowerSource_eq]
            exact hshearExt_meas measurableSet_prod hC_meas (hT_compact a.1).measurableSet |>.inter
              (measurable_snd measurableSet_Iic)
          have hshearExt_map_volumeRestrict_lowerSource :
              Measure.map shearExt (MeasureTheory.volume.restrict lowerSource) =
                MeasureTheory.volume.restrict (shearExt '' lowerSource) := by
            -- Package the ambient same-type transport as a measure identity before using it in the
            -- set-integral rewrite.
            calc
              Measure.map shearExt (MeasureTheory.volume.restrict lowerSource)
                  =
                    (Measure.map shearExt MeasureTheory.volume).restrict
                      (shearExt '' lowerSource) := by
                        simpa [preimage_image_eq _ hshearExt_bijective.1] using
                          (hshearExtEquiv.measurableEmbedding.restrict_map MeasureTheory.volume
                            (shearExt '' lowerSource)).symm
              _ = MeasureTheory.volume.restrict (shearExt '' lowerSource) := by
                    rw [hshearExt_pres.map_eq]
          -- Route correction: use the measurable extension only to build a global measure-level
          -- transport; on `lowerSource` it agrees with the original signed graph coordinates.
          calc
            ∫ q in shear '' lowerSource, rawDiv (splitPull q) ∂MeasureTheory.volume
                = ∫ q in shearExt '' lowerSource, rawDiv (splitPull q) ∂MeasureTheory.volume := by
                    rw [hshearExt_image_eq]
            _ =
                ∫ q in shearExt '' lowerSource,
                  rawDiv (splitPull q)
                    ∂Measure.map shearExt (MeasureTheory.volume.restrict lowerSource) := by
                  rw [← hshearExt_map_volumeRestrict_lowerSource]
            _ =
                ∫ q in lowerSource, rawDiv (splitPull (shearExt q)) ∂MeasureTheory.volume := by
                  simpa [preimage_image_eq _ hshearExt_bijective.1] using
                    (hshearExtEquiv.measurableEmbedding.setIntegral_map
                      (μ := MeasureTheory.volume.restrict lowerSource)
                      (g := fun q : EuclideanSpace ℝ (Fin n) × ℝ ↦ rawDiv (splitPull q))
                      (s := shearExt '' lowerSource))
            _ =
                ∫ q in lowerSource, rawDiv (chartMap q) ∂MeasureTheory.volume := by
                  refine MeasureTheory.setIntegral_congr_fun hlowerSource_meas ?_
                  intro q hq
                  simp [hsplitPull_shearExt_eq_chartMap q hq]
        have hlowerSourceIntegral_eq_topFaceIntegral :
            ∫ q in lowerSource, rawDiv (chartMap q) ∂MeasureTheory.volume =
              topFaceIntegral := by
          have hlowerHalfBox_meas : MeasurableSet lowerHalfBox := by
            -- The fixed product box is measurable because both factors are closed intervals/balls.
            exact Metric.isClosed_closedBall.measurableSet.prod measurableSet_Icc
          have hlowerSourceIntegral_eq_lowerHalfBoxIntegral :
              ∫ q in lowerSource, rawDiv (chartMap q) ∂MeasureTheory.volume =
                ∫ q in lowerHalfBox, rawDiv (chartMap q) ∂MeasureTheory.volume := by
            let boxUnion := lowerSource ∪ lowerHalfBox
            have hboxUnion_meas : MeasurableSet boxUnion := hlowerSource_meas.union hlowerHalfBox_meas
            have hunion_eq_lowerSource :
                ∫ q in boxUnion, rawDiv (chartMap q) ∂MeasureTheory.volume =
                  ∫ q in lowerSource, rawDiv (chartMap q) ∂MeasureTheory.volume := by
              -- Outside `lowerSource` but inside the union, the chart point leaves the support and
              -- the raw divergence vanishes pointwise.
              refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hboxUnion_meas ?_ ?_
              · intro q hq
                exact Or.inl hq
              · intro q hq
                have hq_box : q ∈ lowerHalfBox := by
                  rcases hq.1 with hq_source | hq_box
                  · exact False.elim (hq.2 hq_source)
                  · exact hq_box
                have hq_not_tsupport : chartMap q ∉ tsupport ψloc := by
                  intro hq_support
                  rcases hψloc_subset hq_support with ⟨p, hp, hp_eq⟩
                  have hp_eq_chart :
                      p = (q.1, ψ a.1 q.1 + σ a.1 * q.2) := by
                    have hremoved := congrArg (removeCoordinateMap (i a.1)) hp_eq
                    simpa [chartMap, removeCoordinateMap_insertCoordinateMap] using hremoved
                  have hq_source : q ∈ lowerSource := by
                    refine ⟨?_, hq_box.2.2⟩
                    simpa [hp_eq_chart] using interior_subset hp
                  exact hq.2 hq_source
                exact rawDivergence_eq_zero_of_notMem_tsupport (φ := ψloc) hq_not_tsupport
            have hunion_eq_lowerHalfBox :
                ∫ q in boxUnion, rawDiv (chartMap q) ∂MeasureTheory.volume =
                  ∫ q in lowerHalfBox, rawDiv (chartMap q) ∂MeasureTheory.volume := by
              -- Outside the fixed lower half-box, the flattening support bound shows that the
              -- ambient chart point cannot remain in the topological support.
              refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hboxUnion_meas ?_ ?_
              · intro q hq
                exact Or.inr hq
              · intro q hq
                have hq_source : q ∈ lowerSource := by
                  rcases hq.1 with hq_source | hq_box
                  · exact hq_source
                  · exact False.elim (hq.2 hq_box)
                have hq_not_tsupport : chartMap q ∉ tsupport ψloc := by
                  intro hq_support
                  have hq_flat :
                      q ∈
                        ((fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦
                            (p.1, σ a.1 * (p.2 - ψ a.1 p.1))) ''
                          (removeCoordinateMap (i a.1) '' tsupport ψloc)) := by
                    refine ⟨removeCoordinateMap (i a.1) (chartMap q), ⟨chartMap q, hq_support, rfl⟩, ?_⟩
                    change
                      (((removeCoordinateMap (i a.1) (chartMap q)).1),
                        σ a.1 *
                          (((removeCoordinateMap (i a.1) (chartMap q)).2) -
                            ψ a.1 ((removeCoordinateMap (i a.1) (chartMap q)).1))) = q
                    rw [show removeCoordinateMap (i a.1) (chartMap q) =
                          (q.1, ψ a.1 q.1 + σ a.1 * q.2) by
                          simpa [chartMap] using
                            (removeCoordinateMap_insertCoordinateMap (i a.1)
                              (q.1, ψ a.1 q.1 + σ a.1 * q.2))]
                    ext
                    · simp
                    · rw [show
                            σ a.1 * ((ψ a.1 q.1 + σ a.1 * q.2) - ψ a.1 q.1) =
                              (σ a.1 * σ a.1) * q.2 by ring]
                      simp [hσ_sq]
                  have hq_int := hflat_subset hq_flat
                  rw [interior_prod_eq, Set.mem_prod, interior_Icc, Set.mem_Ioo] at hq_int
                  have hq_box : q ∈ lowerHalfBox := by
                    refine ⟨interior_subset hq_int.1, ?_⟩
                    exact ⟨le_of_lt hq_int.2.1, hq_source.2⟩
                  exact hq.2 hq_box
                exact rawDivergence_eq_zero_of_notMem_tsupport (φ := ψloc) hq_not_tsupport
            calc
              ∫ q in lowerSource, rawDiv (chartMap q) ∂MeasureTheory.volume
                  = ∫ q in boxUnion, rawDiv (chartMap q) ∂MeasureTheory.volume := by
                      symm
                      exact hunion_eq_lowerSource
              _ = ∫ q in lowerHalfBox, rawDiv (chartMap q) ∂MeasureTheory.volume :=
                    hunion_eq_lowerHalfBox
          have hlowerHalfBoxRawDiv_eq_topFaceIntegral :
              ∫ q in lowerHalfBox, rawDiv (chartMap q) ∂MeasureTheory.volume =
                topFaceIntegral := by
            let flatDiv : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := fun q ↦
              ∑ j : Fin (n + 1),
                fderiv ℝ (fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦ eSplit (flatField p)) q
                    (eSplit.symm (EuclideanSpace.single j (1 : ℝ))) j
            have hchartMap_mem_tsupport_imp_baseInterior :
                ∀ {q : EuclideanSpace ℝ (Fin n) × ℝ},
                  chartMap q ∈ tsupport ψloc →
                    q.1 ∈ interior (C a.1) := by
              intro q hq_support
              -- Route correction: pull the ambient support witness back through
              -- `removeCoordinateMap` before reopening the local graph regularity on `C a.1`.
              rcases hψloc_subset hq_support with ⟨p, hp, hp_eq⟩
              have hp_prod :
                  p ∈ interior (C a.1) ×ˢ interior (T a.1) := by
                simpa [interior_prod_eq] using hp
              have hp_eq_chart :
                  p = (q.1, ψ a.1 q.1 + σ a.1 * q.2) := by
                have hremoved := congrArg (removeCoordinateMap (i a.1)) hp_eq
                simpa [chartMap, removeCoordinateMap_insertCoordinateMap] using hremoved
              simpa [hp_eq_chart] using hp_prod.1
            have hflatDiv_eq_rawDivChartMap :
                ∀ q ∈ lowerHalfBox, flatDiv q = rawDiv (chartMap q) := by
              intro q hq
              by_cases hq_support : chartMap q ∈ tsupport ψloc
              · have hq_baseInterior : q.1 ∈ interior (C a.1) :=
                  hchartMap_mem_tsupport_imp_baseInterior hq_support
                -- TODO: on the support branch, expand the chain rule for `eSplit ∘ flatField`,
                -- split the ambient sum into the distinguished `i` coordinate and the
                -- `succAbove` coordinates, and use `hq_baseInterior` to unlock the local `C¹`
                -- regularity of `ψ a.1` before rewriting the product basis vectors through
                -- `removeCoordinateMap_single_self` and `removeCoordinateMap_single_succAbove`.
                sorry
              · have hrawDiv_zero :
                    rawDiv (chartMap q) = 0 := by
                  -- Outside the ambient support, the original localized divergence already
                  -- vanishes.
                  exact rawDivergence_eq_zero_of_notMem_tsupport (φ := ψloc) hq_support
                rw [hrawDiv_zero]
                -- TODO: prove the matching off-support zero-germ statement for
                -- `fun p ↦ eSplit (flatField p)` and then close by
                -- `rawDivergence_eq_zero_of_notMem_tsupport`.
                sorry
            have hlowerHalfBoxFlatDiv_eq_topFaceIntegral :
                ∫ q in lowerHalfBox, flatDiv q ∂MeasureTheory.volume =
                  topFaceIntegral := by
              -- TODO: apply the divergence theorem in the product coordinates transported by
              -- `eSplit`, then use `hflattenedChartField_second_zero` to kill the side and bottom
              -- faces and keep only the top face contribution.
              sorry
            -- Route correction: isolate the algebraic divergence adapter from the geometric
            -- lower-half-box closure so the remaining ambient blocker is no longer monolithic.
            calc
              ∫ q in lowerHalfBox, rawDiv (chartMap q) ∂MeasureTheory.volume
                  = ∫ q in lowerHalfBox, flatDiv q ∂MeasureTheory.volume := by
                      refine MeasureTheory.setIntegral_congr_fun hlowerHalfBox_meas ?_
                      intro q hq
                      rw [hflatDiv_eq_rawDivChartMap q hq]
              _ = topFaceIntegral := hlowerHalfBoxFlatDiv_eq_topFaceIntegral
          -- Route correction: the ambient branch is now reduced to the fixed lower half-box;
          -- only the boxed divergence theorem for `flatField` remains.
          exact
            hlowerSourceIntegral_eq_lowerHalfBoxIntegral.trans
              hlowerHalfBoxRawDiv_eq_topFaceIntegral
        calc
          ∫ x in E,
              (∑ i' : Fin (n + 1), fderiv ℝ ψloc x (EuclideanSpace.single i' (1 : ℝ)) i')
              ∂(domainMeasure Ω)
            =
              ∫ x in chartMap '' lowerSource, rawDiv x ∂(domainMeasure Ω) :=
                hchartIntegral_eq_chartImage
          _ =
              ∫ q in shear '' lowerSource, rawDiv (splitPull q) ∂MeasureTheory.volume :=
                htransportToShear
          _ =
              ∫ q in lowerSource, rawDiv (chartMap q) ∂MeasureTheory.volume :=
                hshearImageIntegral_eq_lowerSourceIntegral
          _ = topFaceIntegral := hlowerSourceIntegral_eq_topFaceIntegral
      have hboundaryFlux_eq_topFaceIntegral :
          ∫ x in frontier E,
            inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb =
              topFaceIntegral := by
        have hboundaryFlux_eq_topImage :
            ∫ x in frontier E,
              inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb =
            ∫ x in chartMap ''
                {q : EuclideanSpace ℝ (Fin n) × ℝ |
                  (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 ∧ q.2 = 0},
              inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb := by
          have hboundaryFlux_eq_boxImage :
              ∫ x in frontier E,
                inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb =
              ∫ x in insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) ∩ frontier E,
                inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb := by
            refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
              isClosed_frontier.measurableSet ?_ ?_
            · intro x hx
              exact hx.2
            · intro x hx
              have hx_not_mem :
                  x ∉ insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) := by
                intro hx_mem
                exact hx.2 ⟨hx_mem, hx.1⟩
              have hx_not_tsupport : x ∉ tsupport ψloc := by
                intro hx_support
                rcases hψloc_subset hx_support with ⟨p, hp, rfl⟩
                exact ⟨p, interior_subset hp, rfl⟩ |> hx_not_mem
              have hx_zero : ψloc x = 0 := image_eq_zero_of_notMem_tsupport hx_not_tsupport
              -- Outside the chart graph patch, the boundary pairing vanishes because `ψloc` does.
              simp [hx_zero]
          have hboxImage_eq_topImage :
              insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) ∩ frontier E =
                chartMap ''
                  {q : EuclideanSpace ℝ (Fin n) × ℝ |
                    (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 ∧ q.2 = 0} := by
            ext x
            exact (htopFaceImage (x := x)).symm
          -- The boundary pairing is now localized to the top-face chart image; only the
          -- codimension-`1` transport to the common density remains.
          calc
            ∫ x in frontier E,
                inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb
              =
                ∫ x in insertCoordinateMap (i a.1) '' (C a.1 ×ˢ T a.1) ∩ frontier E,
                  inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb := hboundaryFlux_eq_boxImage
            _ =
                ∫ x in chartMap ''
                    {q : EuclideanSpace ℝ (Fin n) × ℝ |
                      (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 ∧ q.2 = 0},
                  inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb := by
                  rw [hboxImage_eq_topImage]
        -- TODO: only the codimension-`1` transport remains on the boundary side.
        -- Transport the localized top-image integral to the graph base, rewrite the transported
        -- density with `hflatField_top_commonDensity` on `interior (C a.1)`, and then remove
        -- the off-base contribution using `hflatField_topSecond_zero_outside`.
        let graphMap : EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n) × ℝ := fun z ↦
          (z, ψ a.1 z)
        let topSource : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
          {q | (q.1, ψ a.1 q.1 + σ a.1 * q.2) ∈ C a.1 ×ˢ T a.1 ∧ q.2 = 0}
        have htopImage_eq_splitPullGraph :
            chartMap '' topSource = splitPull '' (graphMap '' C a.1) := by
          -- Normalize the localized top image to the explicit graph over the chart base.
          ext x
          constructor
          · rintro ⟨q, hq, rfl⟩
            refine ⟨(q.1, ψ a.1 q.1), ?_, ?_⟩
            · exact ⟨q.1, hq.1.1, rfl⟩
            · simp [splitPull, chartMap, hq.2]
          · rintro ⟨p, hp, rfl⟩
            rcases hp with ⟨z, hz, rfl⟩
            refine ⟨(z, 0), ?_, ?_⟩
            · constructor
              · simpa using ⟨hz, hψ_memT a.1 z hz⟩
              · simp
            · simp [graphMap, splitPull, chartMap]
        -- TODO: the remaining boundary bridge is now isolated to the explicit graph-patch
        -- parameterization and its density cancellation to `topFaceIntegral`.
        -- Route correction: `splitPull : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin (n + 1))`
        -- is not an isometry for the source product norm (`Prod.norm_def` is the max norm), so
        -- the next plan must avoid a fake `μHE[n]` isometry transport and instead provide a
        -- boundary-space bridge that works in the actual product-coordinate metric.
        have hchartTopImageIntegral_eq_baseWeightedIntegral :
            ∫ x in chartMap '' topSource,
              inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb =
                ∫ z in C a.1,
                  (‖gradient h_boundary.boundary.definingFunction (chartMap (z, 0))‖ /
                      (σ a.1 *
                        gradient h_boundary.boundary.definingFunction (chartMap (z, 0)) (i a.1))) *
                    inner ℝ
                      (ψloc (chartMap (z, 0)))
                      (h_boundary.outwardNormal (chartMap (z, 0))) ∂MeasureTheory.volume := by
          let γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) := fun z ↦
            chartMap (z, 0)
          let weight : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦
            ‖gradient h_boundary.boundary.definingFunction (chartMap (z, 0))‖ /
              (σ a.1 * gradient h_boundary.boundary.definingFunction (chartMap (z, 0)) (i a.1))
          have htopImage_eq_gamma :
              chartMap '' topSource = γ '' C a.1 := by
            ext x
            constructor
            · rintro ⟨q, hq, rfl⟩
              refine ⟨q.1, hq.1.1, ?_⟩
              simpa [γ, chartMap, hq.2]
            · rintro ⟨z, hz, rfl⟩
              refine ⟨(z, 0), ?_, rfl⟩
              refine ⟨?_, by simp⟩
              simpa using ⟨hz, hψ_memT a.1 z hz⟩
          have hgamma_injective : Function.Injective γ := by
            intro z w hzw
            have hremoved := congrArg (removeCoordinateMap (i a.1)) hzw
            have hzws : (z, ψ a.1 z) = (w, ψ a.1 w) := by
              simpa [γ, chartMap, removeCoordinateMap_insertCoordinateMap] using hremoved
            exact congrArg Prod.fst hzws
          have hgammaImage_measure_ne_top :
              μb (γ '' C a.1) ≠ ⊤ := by
            -- The graph image already has finite codimension-`1` surface measure by the compact
            -- graph-image finiteness helper proved earlier in the file.
            simpa [μb, γ, chartMap] using
              graphImage_surfaceMeasure_ne_top (hC_convex a.1) (hC_compact a.1) (hψ_cont a.1)
          have hchartTopSurfaceMeasure_eq_mapWithDensity :
              Measure.map γ
                  ((MeasureTheory.volume.restrict (C a.1)).withDensity
                    (fun z ↦ ENNReal.ofReal (weight z))) =
                μb.restrict (γ '' C a.1) := by
            -- TODO: prove the direct graph-image pushforward identity on `γ '' C a.1`, then use
            -- it as the only boundary transport input for the remaining integral rewrite.
            sorry
          -- Route correction: the remaining boundary task is now a single direct ambient
          -- pushforward along `γ z = chartMap (z, 0)`, with the false `splitPull` isometry route
          -- removed from the proof state entirely.
          rw [htopImage_eq_gamma]
          let γC : C a.1 → EuclideanSpace ℝ (Fin (n + 1)) := fun z ↦ γ z
          let ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
            (MeasureTheory.volume.restrict (C a.1)).withDensity
              (fun z ↦ ENNReal.ofReal (weight z))
          have hγ_cont : ContinuousOn γ (C a.1) := by
            -- The compact-base parameterization only uses the chart regularity already available
            -- on `C a.1`.
            have hgraph_cont :
                ContinuousOn
                  (fun z : EuclideanSpace ℝ (Fin n) ↦ (z, ψ a.1 z))
                  (C a.1) := by
              exact continuousOn_id.prod (hψ_cont a.1).continuousOn
            simpa [γ, chartMap] using
              (insertCoordinateMap (i a.1)).continuous.continuousOn.comp hgraph_cont
          have hγC_meas :
              MeasurableEmbedding γC := by
            -- Restrict to the compact base so the graph parameterization becomes a measurable
            -- embedding without asking for extra global regularity of `ψ a.1`.
            exact ContinuousOn.measurableEmbedding
              (s := C a.1)
              (hs := (hC_compact a.1).measurableSet)
              hγ_cont
              hgamma_injective.injOn
          have hν_restrict :
              ν.restrict (C a.1) = ν := by
            -- The weighted base measure is already supported on `C a.1`.
            dsimp [ν]
            rw [restrict_withDensity (hC_compact a.1).measurableSet]
            simp
          have hmap_gammaC :
              Measure.map γC
                  (Measure.comap ((↑) : C a.1 → EuclideanSpace ℝ (Fin n)) ν) =
                μb.restrict (γ '' C a.1) := by
            -- Repackage the ambient pushforward identity through the measurable embedding of the
            -- compact source chart.
            calc
              Measure.map γC
                  (Measure.comap ((↑) : C a.1 → EuclideanSpace ℝ (Fin n)) ν)
                  =
                    Measure.map γ
                      (Measure.map ((↑) : C a.1 → EuclideanSpace ℝ (Fin n))
                        (Measure.comap ((↑) : C a.1 → EuclideanSpace ℝ (Fin n)) ν)) := by
                          rw [show γC = γ ∘ ((↑) : C a.1 → EuclideanSpace ℝ (Fin n)) by
                                funext z
                                rfl]
                          rw [← Measure.map_map hγC_meas.measurable measurable_subtype_coe]
              _ = Measure.map γ (ν.restrict (C a.1)) := by
                    rw [map_comap_subtype_coe (hC_compact a.1).measurableSet]
              _ = Measure.map γ ν := by rw [hν_restrict]
              _ = μb.restrict (γ '' C a.1) := hchartTopSurfaceMeasure_eq_mapWithDensity
          have htopImageIntegral_eq_baseWithDensity :
              ∫ x in γ '' C a.1,
                inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb =
                  ∫ z in C a.1,
                    inner ℝ
                      (ψloc (γ z))
                      (h_boundary.outwardNormal (γ z)) ∂ν := by
            -- First transport the boundary integral to the compact base through the chart graph.
            calc
              ∫ x in γ '' C a.1,
                  inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb
                =
                  ∫ x in γ '' C a.1,
                    inner ℝ (ψloc x) (h_boundary.outwardNormal x)
                      ∂Measure.map γC
                        (Measure.comap ((↑) : C a.1 → EuclideanSpace ℝ (Fin n)) ν) := by
                          rw [hmap_gammaC]
              _ =
                  ∫ z in γC ⁻¹' (γ '' C a.1),
                    inner ℝ
                      (ψloc (γC z))
                      (h_boundary.outwardNormal (γC z))
                      ∂Measure.comap ((↑) : C a.1 → EuclideanSpace ℝ (Fin n)) ν := by
                        symm
                        exact
                          MeasurableEmbedding.setIntegral_map
                            (μ := Measure.comap ((↑) : C a.1 → EuclideanSpace ℝ (Fin n)) ν)
                            hγC_meas
                            (fun x ↦ inner ℝ (ψloc x) (h_boundary.outwardNormal x))
                            (γ '' C a.1)
              _ =
                  ∫ z : C a.1,
                    inner ℝ
                      (ψloc (γ z))
                      (h_boundary.outwardNormal (γ z))
                      ∂Measure.comap ((↑) : C a.1 → EuclideanSpace ℝ (Fin n)) ν := by
                        simp [γC, hgamma_injective.preimage_image]
              _ =
                  ∫ z in C a.1,
                    inner ℝ
                      (ψloc (γ z))
                      (h_boundary.outwardNormal (γ z)) ∂ν := by
                        simpa [ν] using
                          (MeasureTheory.integral_subtype_comap
                            (μ := ν)
                            (s := C a.1)
                            (hs := (hC_compact a.1).measurableSet)
                            (f := fun z ↦
                              inner ℝ
                                (ψloc (γ z))
                                (h_boundary.outwardNormal (γ z))))
          have hγ_memΩ :
              ∀ z ∈ C a.1, γ z ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
            intro z hz
            exact hbox_subsetΩ ⟨(z, ψ a.1 z), ⟨hz, hψ_memT a.1 z hz⟩, by simp [γ, chartMap]⟩
          have hweight_cont : ContinuousOn weight (C a.1) := by
            have hgrad_cont :
                ContinuousOn
                  (fun z : EuclideanSpace ℝ (Fin n) ↦
                    gradient h_boundary.boundary.definingFunction (γ z))
                  (C a.1) := by
              exact
                ((h_boundary.contDiffOn_gradient Ω.isOpen (fun x hx ↦ hx)).continuousOn).comp
                  hγ_cont hγ_memΩ
            have hnorm_cont :
                ContinuousOn
                  (fun z : EuclideanSpace ℝ (Fin n) ↦
                    ‖gradient h_boundary.boundary.definingFunction (γ z)‖)
                  (C a.1) := by
              exact continuous_norm.continuousOn.comp hgrad_cont
            have hcoord_cont :
                ContinuousOn
                  (fun z : EuclideanSpace ℝ (Fin n) ↦
                    gradient h_boundary.boundary.definingFunction (γ z) (i a.1))
                  (C a.1) := by
              exact
                (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 1) => ℝ)
                  (i a.1)).continuousOn.comp hgrad_cont
            have hden_cont :
                ContinuousOn
                  (fun z : EuclideanSpace ℝ (Fin n) ↦
                    σ a.1 * gradient h_boundary.boundary.definingFunction (γ z) (i a.1))
                  (C a.1) := by
              exact continuous_const.continuousOn.mul hcoord_cont
            refine hnorm_cont.div hden_cont ?_
            intro z hz
            have hz_box : (z, ψ a.1 z) ∈ C a.1 ×ˢ T a.1 := ⟨hz, hψ_memT a.1 z hz⟩
            have hden_pos :
                0 <
                  σ a.1 * gradient h_boundary.boundary.definingFunction (γ z) (i a.1) := by
              simpa [γ, chartMap] using hsign a.1 (z, ψ a.1 z) hz_box
            exact hden_pos.ne'
          have hdensity_aemeas :
              AEMeasurable
                (fun z ↦ ENNReal.ofReal (weight z))
                (MeasureTheory.volume.restrict (C a.1)) := by
            exact
              (ENNReal.continuous_ofReal.continuousOn.comp hweight_cont).aemeasurable
                (hC_compact a.1).measurableSet
          have hdensity_lt_top :
              ∀ᵐ z ∂MeasureTheory.volume.restrict (C a.1),
                ENNReal.ofReal (weight z) < ∞ := by
            filter_upwards with z
            simp
          have hbaseWithDensity_eq_weighted :
              ∫ z in C a.1,
                inner ℝ
                  (ψloc (γ z))
                  (h_boundary.outwardNormal (γ z)) ∂ν
                =
                  ∫ z in C a.1,
                    weight z *
                      inner ℝ
                        (ψloc (γ z))
                        (h_boundary.outwardNormal (γ z)) ∂MeasureTheory.volume := by
            -- Then rewrite the `withDensity` source measure to the explicit scalar weight on `C`.
            dsimp [ν]
            rw [MeasureTheory.setIntegral_withDensity_eq_setIntegral_toReal_smul₀'
              (μ := MeasureTheory.volume)
              (s := C a.1)
              hdensity_aemeas hdensity_lt_top
              (g := fun z ↦ inner ℝ (ψloc (γ z)) (h_boundary.outwardNormal (γ z)))]
            refine MeasureTheory.setIntegral_congr_fun (hC_compact a.1).measurableSet ?_
            intro z hz
            have hz_box : (z, ψ a.1 z) ∈ C a.1 ×ˢ T a.1 := ⟨hz, hψ_memT a.1 z hz⟩
            have hden_pos :
                0 <
                  σ a.1 * gradient h_boundary.boundary.definingFunction (γ z) (i a.1) := by
              simpa [γ, chartMap] using hsign a.1 (z, ψ a.1 z) hz_box
            have hweight_nonneg : 0 ≤ weight z := by
              exact div_nonneg (norm_nonneg _) (le_of_lt hden_pos)
            simp [weight, hweight_nonneg, smul_eq_mul]
          calc
            ∫ x in γ '' C a.1,
                inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb
              =
                ∫ z in C a.1,
                  inner ℝ
                    (ψloc (γ z))
                    (h_boundary.outwardNormal (γ z)) ∂ν :=
                  htopImageIntegral_eq_baseWithDensity
            _ =
                ∫ z in C a.1,
                  weight z *
                    inner ℝ
                      (ψloc (γ z))
                      (h_boundary.outwardNormal (γ z)) ∂MeasureTheory.volume :=
                  hbaseWithDensity_eq_weighted
            _ =
                ∫ z in C a.1,
                  (‖gradient h_boundary.boundary.definingFunction (chartMap (z, 0))‖ /
                      (σ a.1 *
                        gradient h_boundary.boundary.definingFunction (chartMap (z, 0)) (i a.1))) *
                    inner ℝ
                      (ψloc (chartMap (z, 0)))
                      (h_boundary.outwardNormal (chartMap (z, 0))) ∂MeasureTheory.volume := by
                        simp [γ, weight]
        have hboundaryWeightedBaseIntegral_eq_topFaceIntegral :
            ∫ z in C a.1,
              (‖gradient h_boundary.boundary.definingFunction (chartMap (z, 0))‖ /
                  (σ a.1 *
                    gradient h_boundary.boundary.definingFunction (chartMap (z, 0)) (i a.1))) *
                inner ℝ
                  (ψloc (chartMap (z, 0)))
                  (h_boundary.outwardNormal (chartMap (z, 0))) ∂MeasureTheory.volume =
              topFaceIntegral := by
          let topWeight : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦
            (‖gradient h_boundary.boundary.definingFunction (chartMap (z, 0))‖ /
                (σ a.1 *
                  gradient h_boundary.boundary.definingFunction (chartMap (z, 0)) (i a.1))) *
              inner ℝ
                (ψloc (chartMap (z, 0)))
                (h_boundary.outwardNormal (chartMap (z, 0)))
          let topSecond : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦
            (flatField (z, 0)).2
          have htopWeight_eq_topSecond_ae :
              topWeight =ᵐ[MeasureTheory.volume.restrict (C a.1)] topSecond := by
            have hnot_frontier_ae :
                ∀ᵐ z ∂MeasureTheory.volume, z ∉ frontier (C a.1) := by
              rw [MeasureTheory.ae_iff]
              simpa using Convex.addHaar_frontier (μ := MeasureTheory.volume) (hC_convex a.1)
            rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (hC_compact a.1).measurableSet]
            filter_upwards [hnot_frontier_ae] with z hz_not_front hzC
            have hz_int : z ∈ interior (C a.1) := by
              by_contra hz_not_int
              exact hz_not_front ⟨subset_closure hzC, hz_not_int⟩
            -- On the interior of the chart base, cancel the common boundary density by the
            -- distinguished positive gradient factor supplied by `hsign`.
            let A : ℝ :=
              ‖gradient h_boundary.boundary.definingFunction (chartMap (z, 0))‖ *
                inner ℝ
                  (ψloc (chartMap (z, 0)))
                  (h_boundary.outwardNormal (chartMap (z, 0)))
            let B : ℝ :=
              (gradient h_boundary.boundary.definingFunction (chartMap (z, 0))).ofLp (i a.1)
            let den : ℝ :=
              σ a.1 * B
            have hden_pos : 0 < den := by
              have hz_box : (z, ψ a.1 z) ∈ C a.1 ×ˢ T a.1 := by
                exact ⟨hzC, hψ_memT a.1 z hzC⟩
              simpa [den, B, chartMap] using hsign a.1 (z, ψ a.1 z) hz_box
            have hcommon :
                σ a.1 * A = B * topSecond z := by
              simpa [A, B, topSecond, mul_assoc] using
                hflatField_top_commonDensity (z := z) hz_int
            have hscaled :
                A = den * topSecond z := by
              calc
                A = (σ a.1 * σ a.1) * A := by
                  rw [hσ_sq]
                  ring
                _ = σ a.1 * (σ a.1 * A) := by
                  ring
                _ = σ a.1 * (B * topSecond z) := by
                  rw [hcommon]
                _ = (σ a.1 * B) * topSecond z := by
                  ring
                _ = den * topSecond z := by
                  rfl
            have hdiv :
                A / den =
                  topSecond z := by
              have hscaled' :
                  A = topSecond z * den := by
                calc
                  A = den * topSecond z := hscaled
                  _ = topSecond z * den := by
                    ring
              apply (div_eq_iff hden_pos.ne').2
              exact hscaled'
            have hweight :
                topWeight z = A / den := by
              dsimp [topWeight, A, B, den]
              rw [div_mul_eq_mul_div]
            calc
              topWeight z
                  = A / den := hweight
              _ = topSecond z := hdiv
          have hweighted_eq_topSecond :
              ∫ z in C a.1, topWeight z ∂MeasureTheory.volume =
                ∫ z in C a.1, topSecond z ∂MeasureTheory.volume := by
            exact MeasureTheory.integral_congr_ae htopWeight_eq_topSecond_ae
          have htopSecond_union_eq_C :
              ∫ z in C a.1 ∪ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
                topSecond z ∂MeasureTheory.volume =
                  ∫ z in C a.1, topSecond z ∂MeasureTheory.volume := by
            have hunion :
                C a.1 ∪ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R \ C a.1) =
                  C a.1 ∪ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
              ext z
              by_cases hzC : z ∈ C a.1
              · simp [hzC]
              · simp [hzC, or_comm]
            rw [← hunion]
            exact
              MeasureTheory.integral_union_eq_left_of_forall
                ((Metric.isClosed_closedBall.measurableSet.diff (hC_compact a.1).measurableSet))
                (fun z hz ↦
                  hflatField_topSecond_zero_outside (by
                    intro hz_int
                    exact hz.2 (interior_subset hz_int)))
          have htopSecond_union_eq_ball :
              ∫ z in C a.1 ∪ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
                topSecond z ∂MeasureTheory.volume =
                  ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
                    topSecond z ∂MeasureTheory.volume := by
            have hunion :
                Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ∪
                    (C a.1 \ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) =
                  C a.1 ∪ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
              ext z
              by_cases hzB : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R
              · simp [hzB, or_comm]
              · simp [hzB, or_comm, and_left_comm, and_assoc]
            rw [← hunion]
            exact
              MeasureTheory.integral_union_eq_left_of_forall
                (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
                (t := C a.1 \ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
                (μ := MeasureTheory.volume)
                (f := topSecond)
                ((hC_compact a.1).measurableSet.diff Metric.isClosed_closedBall.measurableSet)
                (fun z hz ↦
                  hflatField_topSecond_zero_outsideBall (by
                    intro hz_int
                    exact hz.2 (interior_subset hz_int)))
          -- Route correction: after the explicit weighted graph transport, the remaining work is
          -- purely measure-theoretic bookkeeping on the same compact top face.
          calc
            ∫ z in C a.1, topWeight z ∂MeasureTheory.volume
                = ∫ z in C a.1, topSecond z ∂MeasureTheory.volume :=
                  hweighted_eq_topSecond
            _ =
                ∫ z in C a.1 ∪ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
                  topSecond z ∂MeasureTheory.volume := by
                    symm
                    exact htopSecond_union_eq_C
            _ =
                ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
                  topSecond z ∂MeasureTheory.volume :=
                    htopSecond_union_eq_ball
            _ = topFaceIntegral := by
                  simp [topFaceIntegral, topSecond]
        calc
          ∫ x in frontier E,
              inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb
            =
              ∫ x in chartMap '' topSource,
                inner ℝ (ψloc x) (h_boundary.outwardNormal x) ∂μb :=
                hboundaryFlux_eq_topImage
          _ =
              ∫ z in C a.1,
                (‖gradient h_boundary.boundary.definingFunction (chartMap (z, 0))‖ /
                    (σ a.1 *
                      gradient h_boundary.boundary.definingFunction (chartMap (z, 0)) (i a.1))) *
                  inner ℝ
                    (ψloc (chartMap (z, 0)))
                    (h_boundary.outwardNormal (chartMap (z, 0))) ∂MeasureTheory.volume :=
                hchartTopImageIntegral_eq_baseWeightedIntegral
          _ = topFaceIntegral := hboundaryWeightedBaseIntegral_eq_topFaceIntegral
      -- The chart-local theorem is now reduced to two explicit bridges meeting at one
      -- normalized top-face integral.
      exact hchartIntegral_eq_topFaceIntegral.trans hboundaryFlux_eq_topFaceIntegral.symm
    have nearFieldFlux_ofFiniteCutoffs :
        ∀ s : Finset {x : K // x ∈ t},
          let ρs : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun y ↦
            s.prod (fun b ↦ (1 - χ b y))
          let ψs : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1)) := fun y ↦
            (1 - ρs y) • φ y
          ∫ x in E,
            (∑ i' : Fin (n + 1), fderiv ℝ ψs x (EuclideanSpace.single i' (1 : ℝ)) i')
            ∂(domainMeasure Ω) =
          ∫ x in frontier E,
            inner ℝ (ψs x) (h_boundary.outwardNormal x) ∂μb := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          -- The empty cutoff family gives the zero near field on both sides.
          simp [μb]
      | @insert a s ha ih =>
          let ρs : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun y ↦
            s.prod (fun b ↦ (1 - χ b y))
          let ψs : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1)) := fun y ↦
            (1 - ρs y) • φ y
          let ψpiece : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1)) := fun y ↦
            (χ a y * ρs y) • φ y
          let ψinsert : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1)) := fun y ↦
            (1 - (insert a s).prod (fun b ↦ (1 - χ b y))) • φ y
          have hinsert_split : ∀ y, ψinsert y = ψs y + ψpiece y := by
            intro y
            have hcoeff :=
              congrArg
                (fun r : ℝ ↦ r • φ y)
                (one_sub_cutoffProduct_insert (χ := χ) ha y)
            simpa [ρs, ψs, ψpiece, ψinsert, add_smul] using hcoeff
          have hρs_cont : ContDiff ℝ 1 ρs := by
            -- The old remainder coefficient stays `C¹` under finite products.
            simpa [ρs] using
              (contDiff_prod (t := s) (f := fun b y ↦ 1 - χ b y) fun b hb ↦
                contDiff_const.sub (hχ_cont b))
          have hψs_cont : ContDiff ℝ 1 ψs := by
            -- The accumulated near field remains `C¹`.
            change ContDiff ℝ 1 (((fun y ↦ 1 - ρs y)) • φ)
            simpa [ρs] using (contDiff_const.sub hρs_cont).smul hφ_cont
          have hψs_compact : HasCompactSupport ψs := by
            -- Compact support persists because the near field is still a scalar multiple of `φ`.
            change HasCompactSupport (((fun y ↦ 1 - ρs y)) • φ)
            simpa [ρs] using hφ_compact.smul_left (f := fun y ↦ 1 - ρs y)
          have hψpiece_data :
              ContDiff ℝ 1 ψpiece ∧
                HasCompactSupport ψpiece ∧
                tsupport ψpiece ⊆
                  insertCoordinateMap (i a.1) '' interior (C a.1 ×ˢ T a.1) := by
            -- Package the new chart piece once before the induction step uses it twice.
            simpa [ρs, ψpiece] using
              cutoffWeightedField_chartSupport hχ_cont hχ_compact hχ_subset hφ_cont a s
          rcases hψpiece_data with ⟨hψpiece_cont, hψpiece_compact, hψpiece_subset⟩
          have hψs_diff : Differentiable ℝ ψs := hψs_cont.differentiable_one
          have hψpiece_diff : Differentiable ℝ ψpiece := hψpiece_cont.differentiable_one
          have hdiv_insert_split :
              ∀ x,
                (∑ i' : Fin (n + 1),
                  fderiv ℝ ψinsert x (EuclideanSpace.single i' (1 : ℝ)) i') =
                (∑ i' : Fin (n + 1),
                  fderiv ℝ ψs x (EuclideanSpace.single i' (1 : ℝ)) i') +
                (∑ i' : Fin (n + 1),
                  fderiv ℝ ψpiece x (EuclideanSpace.single i' (1 : ℝ)) i') := by
            intro x
            have hfd :
                fderiv ℝ ψinsert x = fderiv ℝ ψs x + fderiv ℝ ψpiece x := by
              rw [show ψinsert = fun y ↦ ψs y + ψpiece y by
                    funext y
                    exact hinsert_split y]
              exact fderiv_add (hψs_diff x) (hψpiece_diff x)
            -- Rewrite the raw divergence through linearity of the Fréchet derivative.
            simpa [Finset.sum_add_distrib] using
              congrArg
                (fun A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
                    EuclideanSpace ℝ (Fin (n + 1)) ↦
                  ∑ i' : Fin (n + 1), A (EuclideanSpace.single i' (1 : ℝ)) i')
                hfd
          have hdivs_integrable :
              MeasureTheory.Integrable
                (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
                  ∑ i' : Fin (n + 1), fderiv ℝ ψs x (EuclideanSpace.single i' (1 : ℝ)) i')
                (domainMeasure Ω) := by
            -- Compact support keeps the old near-field divergence integrable.
            exact rawDivergenceIntegrable hψs_cont hψs_compact
          have hdivpiece_integrable :
              MeasureTheory.Integrable
                (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
                  ∑ i' : Fin (n + 1), fderiv ℝ ψpiece x (EuclideanSpace.single i' (1 : ℝ)) i')
                (domainMeasure Ω) := by
            -- The new chart piece has the same compact-support divergence integrability.
            exact rawDivergenceIntegrable hψpiece_cont hψpiece_compact
          have hdivs_restrict :
              MeasureTheory.Integrable
                (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
                  ∑ i' : Fin (n + 1), fderiv ℝ ψs x (EuclideanSpace.single i' (1 : ℝ)) i')
                ((domainMeasure Ω).restrict E) :=
            hdivs_integrable.restrict
          have hdivpiece_restrict :
              MeasureTheory.Integrable
                (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
                  ∑ i' : Fin (n + 1), fderiv ℝ ψpiece x (EuclideanSpace.single i' (1 : ℝ)) i')
                ((domainMeasure Ω).restrict E) :=
            hdivpiece_integrable.restrict
          have hfluxs_integrable :
              MeasureTheory.IntegrableOn
                (fun x ↦ inner ℝ (ψs x) (h_boundary.outwardNormal x))
                (frontier E) μb := by
            -- The old boundary pairing is integrable on `frontier E`.
            exact boundaryFluxIntegrable_of_continuous_compactSupport
              h_boundary ψs hψs_cont.continuous hψs_compact
          have hfluxpiece_integrable :
              MeasureTheory.IntegrableOn
                (fun x ↦ inner ℝ (ψpiece x) (h_boundary.outwardNormal x))
                (frontier E) μb := by
            -- The new chart-supported piece is likewise integrable on the frontier.
            exact boundaryFluxIntegrable_of_continuous_compactSupport
              h_boundary ψpiece hψpiece_cont.continuous hψpiece_compact
          calc
            ∫ x in E,
                (∑ i' : Fin (n + 1),
                  fderiv ℝ ψinsert x (EuclideanSpace.single i' (1 : ℝ)) i')
                ∂(domainMeasure Ω)
              =
                ∫ x in E,
                  ((∑ i' : Fin (n + 1),
                      fderiv ℝ ψs x (EuclideanSpace.single i' (1 : ℝ)) i') +
                    ∑ i' : Fin (n + 1),
                      fderiv ℝ ψpiece x (EuclideanSpace.single i' (1 : ℝ)) i')
                  ∂(domainMeasure Ω) := by
                    refine MeasureTheory.integral_congr_ae ?_
                    filter_upwards with x
                    exact hdiv_insert_split x
            _ =
                (∫ x in E,
                  (∑ i' : Fin (n + 1),
                    fderiv ℝ ψs x (EuclideanSpace.single i' (1 : ℝ)) i')
                  ∂(domainMeasure Ω)) +
                ∫ x in E,
                  (∑ i' : Fin (n + 1),
                    fderiv ℝ ψpiece x (EuclideanSpace.single i' (1 : ℝ)) i')
                  ∂(domainMeasure Ω) := by
                    rw [MeasureTheory.integral_add hdivs_restrict hdivpiece_restrict]
            _ =
                (∫ x in frontier E,
                  inner ℝ (ψs x) (h_boundary.outwardNormal x) ∂μb) +
                ∫ x in frontier E,
                  inner ℝ (ψpiece x) (h_boundary.outwardNormal x) ∂μb := by
                    rw [show
                      (∫ x in E,
                        (∑ i' : Fin (n + 1),
                          fderiv ℝ ψs x (EuclideanSpace.single i' (1 : ℝ)) i')
                        ∂(domainMeasure Ω)) =
                        ∫ x in frontier E,
                          inner ℝ (ψs x) (h_boundary.outwardNormal x) ∂μb by
                        simpa [ρs, ψs, μb] using ih]
                    rw [localizedGraphBoxFlux_eq_boundary a ψpiece hψpiece_cont
                      hψpiece_compact hψpiece_subset]
            _ =
                ∫ x in frontier E,
                  (inner ℝ (ψs x) (h_boundary.outwardNormal x) +
                    inner ℝ (ψpiece x) (h_boundary.outwardNormal x)) ∂μb := by
                    rw [← MeasureTheory.integral_add hfluxs_integrable hfluxpiece_integrable]
            _ =
                ∫ x in frontier E,
                  inner ℝ (ψinsert x) (h_boundary.outwardNormal x) ∂μb := by
                    refine MeasureTheory.setIntegral_congr_fun isClosed_frontier.measurableSet ?_
                    intro x hx
                    calc
                      inner ℝ (ψs x) (h_boundary.outwardNormal x) +
                          inner ℝ (ψpiece x) (h_boundary.outwardNormal x)
                        = inner ℝ (ψs x + ψpiece x) (h_boundary.outwardNormal x) := by
                            rw [← inner_add_left]
                      _ = inner ℝ (ψinsert x) (h_boundary.outwardNormal x) := by
                            rw [← hinsert_split x]
    -- With the finset induction in place, the owned theorem now reduces to the current near field.
    change
      ∫ x in E,
        (∑ i' : Fin (n + 1),
          fderiv ℝ (fun y ↦ (1 - t.attach.prod (fun b ↦ (1 - χ b y))) • φ y) x
            (EuclideanSpace.single i' (1 : ℝ)) i')
        ∂(domainMeasure Ω) =
      ∫ x in frontier E,
        inner ℝ ((fun y ↦ (1 - t.attach.prod (fun b ↦ (1 - χ b y))) • φ y) x)
          (h_boundary.outwardNormal x) ∂μb
    simpa [μb] using nearFieldFlux_ofFiniteCutoffs t.attach
  calc
    ∫ x in E,
        (∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(domainMeasure Ω)
      =
        ∫ x in E,
          ((∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i) +
            ∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x
            exact hdiv_split x
    _ =
        (∫ x in E,
          (∑ i : Fin (n + 1), fderiv ℝ φFar x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω)) +
        ∫ x in E,
          (∑ i : Fin (n + 1), fderiv ℝ φNear x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω) := by
            rw [MeasureTheory.integral_add hdivFar_restrict hdivNear_restrict]
    _ =
        0 +
        ∫ x in frontier E,
          inner ℝ (φNear x) (h_boundary.outwardNormal x)
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
            rw [offFrontierDivergence_eq_zero h_boundary φFar hφFar_cont hφFar_compact
              hφFar_subset hφFar_frontier_disjoint]
            rw [hnear]
    _ =
        ∫ x in frontier E,
          inner ℝ (φNear x) (h_boundary.outwardNormal x)
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
            simp
    _ =
        ∫ x in frontier E,
          inner ℝ (φ x) (h_boundary.outwardNormal x)
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
            exact hboundary_eq.symm

/-- Helper for Example 8.12: after normalizing away the Chapter 8 pairing
wrappers, the geometric core is the raw flux identity for a compactly
supported ambient `C¹` field. -/
theorem indicatorDivergence_eq_boundaryFluxSucc
    {n : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hψ_cont : ContDiff ℝ 1 ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hψ_subset : tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    ∫ x in E,
        (∑ i : Fin (n + 1), fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(domainMeasure Ω) =
      ∫ x in frontier E,
        inner ℝ (ψ x) (h_boundary.outwardNormal x)
          ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
  let K : Set (EuclideanSpace ℝ (Fin (n + 1))) := frontier E ∩ tsupport ψ
  have hK_compact : IsCompact K := by
    -- The frontier interaction set is compact because `ψ` has compact support.
    simpa [K, Set.inter_comm] using hψ_compact.isCompact.inter_right isClosed_frontier
  have hK_subset : K ⊆ frontier E := by
    -- The localization core really sits on the frontier.
    intro x hx
    exact hx.1
  obtain ⟨χ, U, L, hU_open, hL_compact, hKL, hχ_cont, hχ_compact, hχ_subsetU,
      hL_subsetU, hU_subset, hχ_one, hχ_range, hU_grad⟩ :=
    h_boundary.existsThickFrontierCutoffWithRegularSupport hK_compact hK_subset
  let ψNear : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := χ • ψ
  let ψFar : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    (fun x ↦ 1 - χ x) • ψ
  have hsplit : ∀ x, ψ x = ψFar x + ψNear x := by
    -- Split `ψ` into the near-frontier piece and its complementary remainder.
    intro x
    simp [ψFar, ψNear, sub_eq_add_neg, add_smul]
  have hψNear_cont : ContDiff ℝ 1 ψNear := by
    -- Multiplying by the smooth cutoff keeps the near-frontier field `C¹`.
    simpa [ψNear] using hχ_cont.smul hψ_cont
  have hψFar_cont : ContDiff ℝ 1 ψFar := by
    -- The complementary field is also `C¹`.
    simpa [ψFar] using (contDiff_const.sub hχ_cont).smul hψ_cont
  have hψNear_compact : HasCompactSupport ψNear := by
    -- The cutoff support controls the near-frontier piece.
    simpa [ψNear] using hχ_compact.smul_right (f' := ψ)
  have hψFar_compact : HasCompactSupport ψFar := by
    -- Compact support of `ψ` controls the off-frontier remainder.
    simpa [ψFar] using hψ_compact.smul_left (f := fun x ↦ 1 - χ x)
  have hψNear_subsetU : tsupport ψNear ⊆ U := by
    -- The near-frontier piece is supported where the cutoff itself is supported.
    exact (tsupport_smul_subset_left χ ψ).trans hχ_subsetU
  have hψNear_subset :
      tsupport ψNear ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The regular neighborhood lies inside the ambient open set.
    exact hψNear_subsetU.trans hU_subset
  have hψFar_subset :
      tsupport ψFar ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The complementary piece still lives inside the original compact support of `ψ`.
    exact (tsupport_smul_subset_right (fun x ↦ 1 - χ x) ψ).trans hψ_subset
  have hψFar_notMem_tsupport : ∀ x ∈ frontier E, x ∉ tsupport ψFar := by
    -- Route correction: the thicker cutoff makes the far piece vanish on a whole
    -- neighborhood of each frontier point, not merely pointwise on the frontier.
    intro x hx
    by_cases hxψ : x ∈ tsupport ψ
    · have hxL : x ∈ interior L := hKL ⟨hx, hxψ⟩
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [isOpen_interior.mem_nhds hxL] with y hy
      have hχy : χ y = 1 := hχ_one (interior_subset hy)
      simp [ψFar, hχy]
    · rw [notMem_tsupport_iff_eventuallyEq] at hxψ
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [hxψ] with y hy
      simp [ψFar, hy]
  have hψFar_frontier_disjoint : tsupport ψFar ∩ frontier E = ∅ := by
    -- The far piece is now genuinely support-disjoint from the frontier.
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hψFar_notMem_tsupport x hx.2 hx.1
  have hψFar_closure_subsetInterior :
      closure (E ∩ tsupport ψFar) ⊆ interior E := by
    -- The support-separated far piece has a compact core contained entirely in the interior.
    simpa using
      h_boundary.closureInterTsupportSubsetInteriorOfFrontierDisjoint
        (φ := ψFar) hψFar_frontier_disjoint
  have hψFar_diff : Differentiable ℝ ψFar := hψFar_cont.differentiable_one
  have hψNear_diff : Differentiable ℝ ψNear := hψNear_cont.differentiable_one
  have hdiv_split :
      ∀ x,
        (∑ i : Fin (n + 1), fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) i) =
          (∑ i : Fin (n + 1), fderiv ℝ ψFar x (EuclideanSpace.single i (1 : ℝ)) i) +
            (∑ i : Fin (n + 1), fderiv ℝ ψNear x (EuclideanSpace.single i (1 : ℝ)) i) := by
    intro x
    have hfd :
        fderiv ℝ ψ x = fderiv ℝ ψFar x + fderiv ℝ ψNear x := by
      rw [show ψ = fun y ↦ ψFar y + ψNear y by
            funext y
            exact hsplit y]
      exact fderiv_add (hψFar_diff x) (hψNear_diff x)
    -- Rewrite the divergence through the linearity of the Fréchet derivative.
    simpa [Finset.sum_add_distrib] using
      congrArg
        (fun A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
            EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), A (EuclideanSpace.single i (1 : ℝ)) i)
        hfd
  have hdivFar_integrable :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ ψFar x (EuclideanSpace.single i (1 : ℝ)) i)
        (domainMeasure Ω) := by
    -- The far-piece divergence remains integrable because the field is `C¹` with compact support.
    exact rawDivergenceIntegrable hψFar_cont hψFar_compact
  have hdivNear_integrable :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ ψNear x (EuclideanSpace.single i (1 : ℝ)) i)
        (domainMeasure Ω) := by
    -- The same compact-support integrability applies to the near-piece divergence.
    exact rawDivergenceIntegrable hψNear_cont hψNear_compact
  have hdivFar_restrict :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ ψFar x (EuclideanSpace.single i (1 : ℝ)) i)
        ((domainMeasure Ω).restrict E) :=
    hdivFar_integrable.restrict
  have hdivNear_restrict :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦
          ∑ i : Fin (n + 1), fderiv ℝ ψNear x (EuclideanSpace.single i (1 : ℝ)) i)
        ((domainMeasure Ω).restrict E) :=
    hdivNear_integrable.restrict
  have hboundary_eq :
      ∫ x in frontier E,
        inner ℝ (ψ x) (h_boundary.outwardNormal x)
          ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) =
      ∫ x in frontier E,
        inner ℝ (ψNear x) (h_boundary.outwardNormal x)
          ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
    refine MeasureTheory.setIntegral_congr_fun isClosed_frontier.measurableSet ?_
    intro x hx
    have hψFar_zero : ψFar x = 0 := image_eq_zero_of_notMem_tsupport (hψFar_notMem_tsupport x hx)
    -- On the frontier the far piece vanishes, so only the near piece contributes.
    calc
      inner ℝ (ψ x) (h_boundary.outwardNormal x)
        = inner ℝ (ψFar x + ψNear x) (h_boundary.outwardNormal x) := by
            rw [hsplit x]
      _ = inner ℝ (ψNear x) (h_boundary.outwardNormal x) := by
            simp [hψFar_zero]
  -- Route correction: the successor-dimensional theorem is now reduced to two
  -- companion lemmas with stable statements:
  -- `offFrontierDivergence_eq_zero` for the far piece and
  -- `regularNeighborhoodFlux_eq_boundary` for the near piece.
  calc
    ∫ x in E,
        (∑ i : Fin (n + 1), fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(domainMeasure Ω)
      =
        ∫ x in E,
          ((∑ i : Fin (n + 1), fderiv ℝ ψFar x (EuclideanSpace.single i (1 : ℝ)) i) +
            ∑ i : Fin (n + 1), fderiv ℝ ψNear x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x
            exact hdiv_split x
    _ =
        (∫ x in E,
          (∑ i : Fin (n + 1), fderiv ℝ ψFar x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω)) +
        ∫ x in E,
          (∑ i : Fin (n + 1), fderiv ℝ ψNear x (EuclideanSpace.single i (1 : ℝ)) i)
          ∂(domainMeasure Ω) := by
            rw [MeasureTheory.integral_add hdivFar_restrict hdivNear_restrict]
    _ =
        0 +
        ∫ x in frontier E,
          inner ℝ (ψNear x) (h_boundary.outwardNormal x)
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
            rw [offFrontierDivergence_eq_zero h_boundary ψFar hψFar_cont hψFar_compact
              hψFar_subset hψFar_frontier_disjoint]
            rw [regularNeighborhoodFlux_eq_boundary h_boundary hU_open hU_subset hU_grad
              ψNear hψNear_cont hψNear_compact hψNear_subsetU]
    _ =
        ∫ x in frontier E,
          inner ℝ (ψNear x) (h_boundary.outwardNormal x)
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
            simp
    _ =
        ∫ x in frontier E,
          inner ℝ (ψ x) (h_boundary.outwardNormal x)
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure n) := by
            exact hboundary_eq.symm

/-- Helper for Example 8.12: after normalizing away the Chapter 8 pairing
wrappers, the geometric core is the raw flux identity for a compactly
supported ambient `C¹` field. -/
theorem indicatorDivergence_eq_boundaryFlux
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    (ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hψ_cont : ContDiff ℝ 1 ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hψ_subset : tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    ∫ x in E,
        (∑ i : Fin d, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(domainMeasure Ω) =
      ∫ x in frontier E,
        inner ℝ (ψ x) (h_boundary.outwardNormal x)
          ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) := by
  cases d with
  | zero =>
      have hfrontier : frontier E = ∅ := frontier_eq_empty_of_zeroDim h_boundary
      -- In the degenerate zero-dimensional branch, the divergence sum is empty and the frontier vanishes.
      rw [hfrontier]
      simp
  | succ n =>
      -- Route correction: isolate the only live geometric blocker in the successor-dimensional helper.
      simpa using
        HasC2BoundaryIn.indicatorDivergence_eq_boundaryFluxSucc
          h_boundary ψ hψ_cont hψ_compact hψ_subset

/-- A `C²` boundary in `Ω` yields the boundary-pairing formula from Example 8.12
for indicator data using the defining-function outward unit normal. -/
theorem boundary_pairing
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {f₀ : ℝ}
    {hE_meas : MeasurableSet E}
    {hE_finite : VariationalRegularization.domainMeasure Ω E ≠ ⊤}
    (v : AdmissibleTestField Ω) :
    admissibleDivergencePairing
        (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) v =
      f₀ *
        ∫ x in frontier E,
          inner ℝ (v.toTestFunction x) (h_boundary.outwardNormal x)
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) := by
  obtain ⟨hv_cont, hv_compact, hv_subset, _hv_norm⟩ := v.spec
  have hindicator :
      (fun x =>
          MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀ x *
            admissibleDivergence v x) =ᵐ[domainMeasure Ω]
        fun x => E.indicator (fun y => f₀ * admissibleDivergence v y) x := by
    -- Replace the `Lp` indicator datum by its pointwise indicator representative.
    have hIndicatorConst :
        (fun x => MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀ x) =ᵐ[domainMeasure Ω]
          E.indicator (fun _ => f₀) := by
      simpa using
        (@MeasureTheory.indicatorConstLp_coeFn
          (EuclideanSpace ℝ (Fin d)) ℝ _ (1 : ENNReal) (domainMeasure Ω) _ E
          hE_meas hE_finite f₀)
    filter_upwards [hIndicatorConst] with x hx
    by_cases hxE : x ∈ E
    · simp [hx, hxE, admissibleDivergence]
    · simp [hx, hxE, admissibleDivergence]
  -- Expand the Chapter 8 pairing, rewrite it as a set integral over `E`, and then
  -- hand the geometry to the raw flux theorem above.
  rw [admissibleDivergencePairing_def]
  calc
    ∫ x,
        MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀ x *
          admissibleDivergence v x ∂domainMeasure Ω
        =
          ∫ x, E.indicator (fun y => f₀ * admissibleDivergence v y) x ∂domainMeasure Ω := by
            exact MeasureTheory.integral_congr_ae hindicator
    _ = ∫ x in E, f₀ * admissibleDivergence v x ∂domainMeasure Ω := by
          simpa using
            (MeasureTheory.integral_indicator
              (μ := domainMeasure Ω)
              (f := fun y => f₀ * admissibleDivergence v y)
              hE_meas)
    _ = f₀ * ∫ x in E, admissibleDivergence v x ∂domainMeasure Ω := by
          rw [MeasureTheory.integral_const_mul]
    _ =
        f₀ *
          ∫ x in frontier E,
            inner ℝ (v.toTestFunction x) (h_boundary.outwardNormal x)
              ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) := by
          congr 1
          -- The remaining proof obligation is exactly the raw ambient-field flux identity.
          simpa [admissibleDivergence_def] using
            h_boundary.indicatorDivergence_eq_boundaryFlux
              v.toTestFunction hv_cont hv_compact hv_subset

end HasC2BoundaryIn

/-- Helper for Example 8.12: a compact frontier cutoff supported on a regular
neighborhood should produce the localized signed-normal admissible witness used
in the lower-bound theorem. -/
theorem HasC2BoundaryIn.existsLocalizedSignedNormalAdmissible
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {f₀ : ℝ}
    {hE_meas : MeasurableSet E}
    {hE_finite : VariationalRegularization.domainMeasure Ω E ≠ ⊤}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ, ∃ v : AdmissibleTestField Ω,
      Continuous χ ∧
      HasCompactSupport χ ∧
      Set.EqOn χ 1 K ∧
      (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
      admissibleDivergencePairing
          (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) v =
        |f₀| *
          ∫ x in frontier E, χ x
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) := by
  obtain ⟨χ, U, hU_open, hχ_cont, hχ_compact, hχ_subsetU, hU_subset, hχ_one, hχ_range, hU_grad⟩ :=
    h_boundary.existsFrontierCutoffWithRegularSupport hK_compact hK_subset
  let ν : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x ↦
    ((‖gradient h_boundary.boundary.definingFunction x‖)⁻¹ : ℝ) •
      gradient h_boundary.boundary.definingFunction x
  let ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    (fun x ↦ Real.sign f₀ * χ x) • ν
  have hν_cont : ContDiffOn ℝ 1 ν U := by
    -- The normalized gradient is `C¹` on the regular neighborhood carrying the cutoff support.
    simpa [ν] using
      contDiffOn_normalizedGradient h_boundary hU_open hU_subset hU_grad
  have hψ_cont : ContDiff ℝ 1 ψ := by
    -- The witness field is smooth on `U`, and outside `U` it vanishes near each point because
    -- the cutoff support stays inside `U`.
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxU : x ∈ U
    · have hχx : ContDiffAt ℝ 1 χ x := hχ_cont.contDiffAt
      have hνx : ContDiffAt ℝ 1 ν x := hν_cont.contDiffAt (hU_open.mem_nhds hxU)
      simpa [ψ] using ((contDiffAt_const.mul hχx).smul hνx)
    · have hxχ : x ∉ tsupport χ := by
        exact fun hxχ ↦ hxU (hχ_subsetU hxχ)
      have hχ_zero : χ =ᶠ[nhds x] 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at hxχ
      have hψ_zero : ψ =ᶠ[nhds x] (fun _ ↦ 0) := by
        filter_upwards [hχ_zero] with y hy
        simp [ψ, hy]
      simpa using
        (ContDiffAt.congr_of_eventuallyEq
          (x := x) (f := fun _ ↦ (0 : EuclideanSpace ℝ (Fin d))) (f₁ := ψ)
          (contDiffAt_const : ContDiffAt ℝ 1 (fun _ ↦ (0 : EuclideanSpace ℝ (Fin d))) x)
          hψ_zero)
  have hscalar_compact : HasCompactSupport (fun x ↦ Real.sign f₀ * χ x) := by
    simpa [Pi.mul_def, mul_comm] using
      (HasCompactSupport.mul_right
        (f := χ) (f' := fun _ : EuclideanSpace ℝ (Fin d) ↦ Real.sign f₀) hχ_compact)
  have hψ_compact : HasCompactSupport ψ := by
    simpa [ψ] using hscalar_compact.smul_right (f' := ν)
  have hscalar_tsupport :
      tsupport (fun x ↦ Real.sign f₀ * χ x) ⊆ tsupport χ := by
    simpa [Pi.mul_def, mul_comm] using
      (tsupport_mul_subset_left
        (f := χ) (g := fun _ : EuclideanSpace ℝ (Fin d) ↦ Real.sign f₀))
  have hψ_subset :
      tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
    exact
      (tsupport_smul_subset_left (fun x ↦ Real.sign f₀ * χ x) ν).trans
        (hscalar_tsupport.trans (hχ_subsetU.trans hU_subset))
  have hψ_norm :
      ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))), ‖ψ x‖ ≤ 1 := by
    intro x _hxΩ
    by_cases hxχ : x ∈ tsupport χ
    · have hxU : x ∈ U := hχ_subsetU hxχ
      have hsign_le : |Real.sign f₀| ≤ 1 := by
        rcases lt_trichotomy f₀ 0 with hf₀ | rfl | hf₀
        · simp [Real.sign_of_neg hf₀]
        · simp
        · simp [Real.sign_of_pos hf₀]
      have hχ_nonneg : 0 ≤ χ x := (hχ_range x).1
      have hχ_le : χ x ≤ 1 := (hχ_range x).2
      rw [show ψ x = (Real.sign f₀ * χ x) • ν x by rfl, norm_smul, Real.norm_eq_abs,
        show ‖ν x‖ = 1 by
          simpa [ν] using norm_normalizedGradient_eq_one (hU_grad x hxU), mul_one]
      rw [abs_mul, abs_of_nonneg hχ_nonneg]
      exact
        (mul_le_mul hsign_le hχ_le hχ_nonneg (by norm_num : (0 : ℝ) ≤ 1)).trans <| by
          norm_num
    · simp [ψ, image_eq_zero_of_notMem_tsupport hxχ]
  obtain ⟨v, hv_eq⟩ :=
    contDiffFieldToAdmissibleTestField ψ hψ_cont hψ_compact hψ_subset hψ_norm
  refine ⟨χ, v, hχ_cont.continuous, hχ_compact, hχ_one, hχ_range, ?_⟩
  have hv_pairing :=
    h_boundary.boundary_pairing (f₀ := f₀) (hE_meas := hE_meas) (hE_finite := hE_finite) v
  calc
    admissibleDivergencePairing
        (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) v
      =
        f₀ *
          ∫ x in frontier E,
            inner ℝ (v.toTestFunction x) (h_boundary.outwardNormal x)
              ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) := by
          simpa using hv_pairing
    _ =
        f₀ *
          ∫ x in frontier E,
            Real.sign f₀ * χ x
              ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) := by
          congr 1
          refine MeasureTheory.setIntegral_congr_fun isClosed_frontier.measurableSet ?_
          intro x hx
          have hvx :
              v.toTestFunction x =
                (Real.sign f₀ * χ x) • h_boundary.outwardNormal x := by
            calc
              v.toTestFunction x = ψ x := hv_eq x
              _ = (Real.sign f₀ * χ x) • ν x := by rfl
              _ = (Real.sign f₀ * χ x) • h_boundary.outwardNormal x := by
                simpa [ν] using congrArg
                  (fun z ↦ (Real.sign f₀ * χ x) • z)
                  (normalizedGradient_eq_outwardNormal_onFrontier h_boundary hx)
          calc
            inner ℝ (v.toTestFunction x) (h_boundary.outwardNormal x)
              = inner ℝ ((Real.sign f₀ * χ x) • h_boundary.outwardNormal x)
                  (h_boundary.outwardNormal x) := by simpa [hvx]
            _ = Real.sign f₀ * χ x := by
              rw [real_inner_smul_left, real_inner_self_eq_norm_sq,
                h_boundary.isOutwardNormal.norm_eq_one x hx]
              ring
    _ = (f₀ * Real.sign f₀) *
          ∫ x in frontier E, χ x
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) := by
          rw [MeasureTheory.integral_const_mul, mul_assoc]
    _ = |f₀| *
          ∫ x in frontier E, χ x
            ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) := by
          rw [mul_sign_eq_abs]

/-- Helper for Example 8.12: if `frontier E ∩ tsupport χ` has finite
codimension-`1` Hausdorff measure, then a cutoff equal to `1` on `K` controls
the Hausdorff mass of `K` by its frontier integral. -/
theorem frontierCutoffMeasure_le_surfaceIntegral_of_supportMeasure_ne_top
    {d : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ_cont : Continuous χ)
    (hχ_compact : HasCompactSupport χ)
    (hχ_one : Set.EqOn χ 1 K)
    (hχ_range : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hfrontierSupport_ne_top :
      (MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1))
        (frontier E ∩ tsupport χ) ≠ ⊤) :
    ((MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) K : EReal) ≤
      (((∫ x in frontier E, χ x
          ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) : ℝ)) : EReal) := by
  let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) :=
    MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)
  have htsupport_meas : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hfrontierSupport_meas : MeasurableSet (frontier E ∩ tsupport χ) :=
    isClosed_frontier.measurableSet.inter htsupport_meas
  have hμ_restrict_tsupport_ne_top :
      (μ.restrict (frontier E)) (tsupport χ) ≠ ⊤ := by
    -- Restricting to the frontier turns the support-mass hypothesis into a finite-measure
    -- statement on the compact support itself.
    simpa [μ, MeasureTheory.Measure.restrict_apply, htsupport_meas, Set.inter_comm] using
      hfrontierSupport_ne_top
  have hχ_nonneg : 0 ≤ᵐ[μ.restrict (frontier E)] χ := by
    -- The cutoff range hypothesis gives the nonnegativity needed for all frontier integrals.
    exact Filter.Eventually.of_forall (fun x ↦ (hχ_range x).1)
  have hχ_integrable_on_support :
      MeasureTheory.IntegrableOn χ (tsupport χ) (μ.restrict (frontier E)) := by
    -- Once the frontier-restricted support has finite measure, continuity on the compact support
    -- gives integrability there.
    exact hχ_cont.continuousOn.integrableOn_of_subset_isCompact
      hχ_compact htsupport_meas subset_rfl hμ_restrict_tsupport_ne_top
  have hχ_integrable_frontier :
      MeasureTheory.IntegrableOn χ (frontier E) μ := by
    -- Because `χ` vanishes outside its support, integrability on the support upgrades to the whole
    -- frontier after restricting the ambient measure.
    have hχ_integrable_restrict : MeasureTheory.Integrable (μ := μ.restrict (frontier E)) χ := by
      exact
        (MeasureTheory.integrableOn_iff_integrable_of_support_subset (subset_tsupport χ)).mp
          hχ_integrable_on_support
    simpa [MeasureTheory.IntegrableOn] using hχ_integrable_restrict
  have hK_subset_tsupport : K ⊆ tsupport χ := by
    -- On `K` the cutoff takes the nonzero value `1`, so `K` lies inside the topological support.
    intro x hx
    refine subset_tsupport χ ?_
    simpa [Function.mem_support, hχ_one hx]
  have hK_subset_frontierSupport : K ⊆ frontier E ∩ tsupport χ := by
    intro x hx
    exact ⟨hK_subset hx, hK_subset_tsupport hx⟩
  have hμK_ne_top : μ K ≠ ⊤ := by
    -- The compact piece inherits finite measure from the finite support-localized frontier patch.
    exact MeasureTheory.measure_ne_top_of_subset hK_subset_frontierSupport hfrontierSupport_ne_top
  have hχK_eq_one :
      ∫ x in K, χ x ∂μ = ∫ x in K, (1 : ℝ) ∂μ := by
    -- On the compact piece, the cutoff is exactly `1`.
    refine MeasureTheory.setIntegral_congr_fun hK_compact.isClosed.measurableSet ?_
    intro x hx
    exact hχ_one hx
  have hχ_mono :
      ∫ x in K, χ x ∂μ ≤ ∫ x in frontier E, χ x ∂μ := by
    -- Enlarge the integration set from `K` to `frontier E` using `χ ≥ 0`.
    exact MeasureTheory.setIntegral_mono_set
      (μ := μ)
      (s := K)
      (t := frontier E)
      hχ_integrable_frontier
      hχ_nonneg
      (Filter.Eventually.of_forall hK_subset)
  have hfrontier_nonneg : 0 ≤ ∫ x in frontier E, χ x ∂μ := by
    -- The frontier integral stays nonnegative because the cutoff itself is nonnegative there.
    simpa using MeasureTheory.integral_nonneg_of_ae (μ := μ.restrict (frontier E)) hχ_nonneg
  have hμ_le :
      μ K ≤ ENNReal.ofReal (∫ x in frontier E, χ x ∂μ) := by
    -- Rewrite the compact mass as `∫_K 1`, replace `1` by `χ` on `K`, and then
    -- compare the two set integrals by monotonicity.
    calc
      μ K = ENNReal.ofReal (∫ x in K, (1 : ℝ) ∂μ) := by
        symm
        exact MeasureTheory.ofReal_setIntegral_one_of_measure_ne_top hμK_ne_top
      _ = ENNReal.ofReal (∫ x in K, χ x ∂μ) := by
        rw [hχK_eq_one]
      _ ≤ ENNReal.ofReal (∫ x in frontier E, χ x ∂μ) := by
        exact ENNReal.ofReal_le_ofReal hχ_mono
  have hμ_le_real :
      (μ K).toReal ≤ ∫ x in frontier E, χ x ∂μ := by
    -- Move the ENNReal estimate back to real numbers, where the theorem statement lives.
    simpa [ENNReal.toReal_ofReal hfrontier_nonneg] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ_le
  -- Convert the ENNReal comparison back to the `EReal` statement used by the
  -- Example 8.12 lower-bound assembly.
  calc
    (μ K : EReal) = ((μ K).toReal : EReal) := by
      exact (EReal.coe_ennreal_toReal hμK_ne_top).symm
    _ ≤ ((∫ x in frontier E, χ x ∂μ : ℝ) : EReal) := by
      exact_mod_cast hμ_le_real

/-- Helper for Example 8.12: a `C²` boundary has finite codimension-`1`
Hausdorff mass on each compactly supported frontier patch. -/
lemma frontierSupportSurfaceMeasure_ne_top
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ_compact : HasCompactSupport χ) :
    (MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1))
      (frontier E ∩ tsupport χ) ≠ ⊤ := by
  have hK_compact : IsCompact (frontier E ∩ tsupport χ) := by
    -- The support-localized frontier piece is compact because `χ` has compact support.
    simpa [Set.inter_comm] using hχ_compact.isCompact.inter_right isClosed_frontier
  -- Route correction: expose the actual geometric content as a compact-frontier
  -- finiteness lemma instead of pretending compact support alone suffices.
  exact h_boundary.compactFrontierSurfaceMeasure_ne_top hK_compact fun x hx => hx.1

theorem HasC2BoundaryIn.frontierCutoffMeasure_le_surfaceIntegral
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ_cont : Continuous χ)
    (hχ_compact : HasCompactSupport χ)
    (hχ_one : Set.EqOn χ 1 K)
    (hχ_range : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    ((MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) K : EReal) ≤
      (((∫ x in frontier E, χ x
          ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) : ℝ)) : EReal) := by
  -- Route correction: the measure comparison is now isolated to the compactly
  -- supported cutoff case produced by `existsLocalizedSignedNormalAdmissible`, and the only
  -- remaining side condition is that the compact support-localized frontier patch has finite
  -- Hausdorff measure.
  have hfrontierSupport_ne_top :
      (MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1))
        (frontier E ∩ tsupport χ) ≠ ⊤ := by
    -- Route correction: this finiteness input really comes from the regular
    -- boundary structure, not from compact support alone.
    exact frontierSupportSurfaceMeasure_ne_top h_boundary hχ_compact
  exact frontierCutoffMeasure_le_surfaceIntegral_of_supportMeasure_ne_top
    (K := K) hK_compact hK_subset hχ_cont hχ_compact hχ_one hχ_range
    hfrontierSupport_ne_top

/-- Helper for Example 8.12: a compact frontier piece already contributes its
full boundary mass to the total variation of an indicator datum. -/
theorem HasC2BoundaryIn.compactFrontierMeasure_le_totalVariationIndicatorConst
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    (h_boundary : HasC2BoundaryIn Ω E)
    {f₀ : ℝ}
    {hE_meas : MeasurableSet E}
    {hE_finite : VariationalRegularization.domainMeasure Ω E ≠ ⊤}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ frontier E) :
    ((|f₀| : ℝ) : EReal) *
        ((MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1))
          K : EReal) ≤
      VariationalRegularization.totalVariation
        (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) := by
  cases d with
  | zero =>
      have hfrontier : frontier E = ∅ := HasC2BoundaryIn.frontier_eq_empty_of_zeroDim h_boundary
      have hK_empty : K = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        simpa [hfrontier] using hK_subset hx
      -- Once the frontier vanishes, every compact frontier piece is empty and the lower bound is trivial.
      simpa [hK_empty] using
        HasC2BoundaryIn.totalVariation_nonneg
          (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀)
  | succ n =>
      let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
        MeasureTheory.Measure.euclideanHausdorffMeasure n
      obtain ⟨χ, v, hχ_cont, hχ_compact, hχ_one, hχ_range, hv_pairing⟩ :=
        h_boundary.existsLocalizedSignedNormalAdmissible
          (f₀ := f₀) (hE_meas := hE_meas) (hE_finite := hE_finite)
          hK_compact hK_subset
      have hμ_le :
          (μ K : EReal) ≤
            (((∫ x in frontier E, χ x ∂μ : ℝ)) : EReal) := by
        -- The compact theorem now factors the geometric lower bound through a single
        -- frontier-cutoff comparison lemma.
        simpa [μ] using
          h_boundary.frontierCutoffMeasure_le_surfaceIntegral
            (K := K) hK_compact hK_subset hχ_cont hχ_compact hχ_one hχ_range
      have hpair_le :
          (((|f₀| * ∫ x in frontier E, χ x ∂μ : ℝ)) : EReal) ≤
            VariationalRegularization.totalVariation
              (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) := by
        -- The localized signed-normal witness attains the cutoff surface integral in the pairing.
        have hv_pairing' :
            (((|f₀| * ∫ x in frontier E, χ x ∂μ : ℝ)) : EReal) =
              (admissibleDivergencePairing
                (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) v : EReal) := by
          simpa [μ] using congrArg (fun t : ℝ ↦ (t : EReal)) hv_pairing.symm
        rw [hv_pairing']
        exact admissibleDivergencePairing_le_totalVariation
          (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) v
      have habs_nonneg : 0 ≤ ((|f₀| : ℝ) : EReal) := by
        exact_mod_cast abs_nonneg f₀
      have hmul_le :
          ((|f₀| : ℝ) : EReal) * (μ K : EReal) ≤
            ((|f₀| : ℝ) : EReal) *
              ((((∫ x in frontier E, χ x ∂μ : ℝ)) : EReal)) := by
        exact mul_le_mul_of_nonneg_left hμ_le habs_nonneg
      calc
        ((|f₀| : ℝ) : EReal) * (μ K : EReal)
            ≤ ((|f₀| : ℝ) : EReal) *
                ((((∫ x in frontier E, χ x ∂μ : ℝ)) : EReal)) := hmul_le
        _ = (((|f₀| * ∫ x in frontier E, χ x ∂μ : ℝ)) : EReal) := by
          rw [← EReal.coe_mul]
        _ ≤ VariationalRegularization.totalVariation
              (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) := hpair_le

/-- Under a packaged `C²` boundary hypothesis, the boundary pairing formula for
an indicator datum bounds the Chapter 8 divergence pairing by `|f₀|` times the
codimension-`1` Euclidean Hausdorff measure of `frontier E`. -/
theorem indicatorConst_pairing_le_surfaceArea_of_boundaryFormula
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    {f₀ : ℝ}
    (h_boundary : HasC2BoundaryIn Ω E)
    (hE_meas : MeasurableSet E)
    (hE_finite : VariationalRegularization.domainMeasure Ω E ≠ ⊤)
    (v : AdmissibleTestField Ω) :
    (admissibleDivergencePairing
        (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) v : EReal) ≤
      ((|f₀| : ℝ) : EReal) *
        ((MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1))
          (frontier E) : EReal) := by
  let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) :=
    MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)
  by_cases hμtop : μ (frontier E) = ⊤
  · by_cases hf₀ : f₀ = 0
    · subst f₀
      rw [h_boundary.boundary_pairing v]
      simp
    · have hrhs :
        ((|f₀| : ℝ) : EReal) * (μ (frontier E) : EReal) = ⊤ := by
        rw [hμtop]
        simpa using EReal.coe_mul_top_of_pos (abs_pos.mpr hf₀)
      rw [hrhs]
      exact le_top
  · have hIntAbs :
      |∫ x in frontier E, inner ℝ (v.toTestFunction x) (h_boundary.outwardNormal x) ∂μ|
        ≤ 1 * μ.real (frontier E) := by
      simpa [Real.norm_eq_abs] using
        (MeasureTheory.norm_setIntegral_le_of_norm_le_const
          (lt_top_iff_ne_top.mpr hμtop)
          (fun x hx ↦ boundaryInner_norm_le_one
            h_boundary.frontier_subset h_boundary.outwardNormal
            h_boundary.isOutwardNormal.norm_eq_one v hx))
    have hreal :
        admissibleDivergencePairing
            (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) v
          ≤ |f₀| * μ.real (frontier E) := by
      calc
        admissibleDivergencePairing
            (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) v
            = f₀ *
                ∫ x in frontier E,
                  inner ℝ (v.toTestFunction x) (h_boundary.outwardNormal x) ∂μ := by
                    simpa [μ] using h_boundary.boundary_pairing v
        _ ≤ |f₀| *
              |∫ x in frontier E,
                  inner ℝ (v.toTestFunction x) (h_boundary.outwardNormal x) ∂μ| := by
          have hpair_abs :
              |f₀ * ∫ x in frontier E,
                  inner ℝ (v.toTestFunction x) (h_boundary.outwardNormal x) ∂μ|
                ≤ |f₀| *
                    |∫ x in frontier E,
                        inner ℝ (v.toTestFunction x) (h_boundary.outwardNormal x) ∂μ| := by
            rw [abs_mul]
          exact (le_abs_self _).trans hpair_abs
        _ ≤ |f₀| * (1 * μ.real (frontier E)) := by
          exact mul_le_mul_of_nonneg_left hIntAbs (abs_nonneg f₀)
        _ = |f₀| * μ.real (frontier E) := by ring
    have hmeasure_cast :
        ((μ.real (frontier E) : ℝ) : EReal) = (μ (frontier E) : EReal) := by
      have hcoe_toReal :
          (((μ (frontier E) : EReal).toReal : ℝ) : EReal) = (μ (frontier E) : EReal) :=
        EReal.coe_toReal (by simpa using hμtop) (by simp)
      simpa [MeasureTheory.Measure.real, μ] using
        hcoe_toReal
    have hreal_cast :
        (admissibleDivergencePairing
            (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) v : EReal)
          ≤ ((|f₀| * μ.real (frontier E) : ℝ) : EReal) := by
      exact_mod_cast hreal
    calc
      (admissibleDivergencePairing
          (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) v : EReal)
          ≤ ((|f₀| * μ.real (frontier E) : ℝ) : EReal) := hreal_cast
      _ = ((|f₀| : ℝ) : EReal) * ((μ.real (frontier E) : ℝ) : EReal) := by
        rw [← EReal.coe_mul]
      _ = ((|f₀| : ℝ) : EReal) * (μ (frontier E) : EReal) := by
        rw [hmeasure_cast]

end VariationalRegularization
