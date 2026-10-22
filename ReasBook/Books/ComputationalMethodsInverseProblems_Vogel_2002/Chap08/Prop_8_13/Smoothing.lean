/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_13.Sobolev
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Geometry.Manifold.PartitionOfUnity

public section

noncomputable section

namespace VariationalRegularization

open scoped ContDiff

variable {d : ℕ}

/-- Helper for Proposition 8.13: a function supported in `Ω` admits a smooth
scalar cutoff that is identically `1` on its topological support and vanishes
outside `Ω`. -/
lemma existsSmoothUnitCutoffOnSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsub : tsupport u ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    ∃ η : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ η ∧
      Set.EqOn η 1 (tsupport u) ∧
      (∀ x ∉ (Ω : Set (EuclideanSpace ℝ (Fin d))), η x = 0) ∧
      (∀ x, η x ∈ Set.Icc (0 : ℝ) 1) := by
  have hsClosed : IsClosed (tsupport u) := isClosed_tsupport u
  have hsInterior :
      tsupport u ⊆ interior ((Ω : Set (EuclideanSpace ℝ (Fin d)))) := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr <| Ω.2.mem_nhds (hsub hx)
  rcases exists_contMDiffMap_one_nhds_of_subset_interior
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d)))
      (M := EuclideanSpace ℝ (Fin d))
      (n := (⊤ : ℕ∞)) hsClosed hsInterior with ⟨η, hη_one, hη_zero, hη_range⟩
  refine ⟨η.1, ?_, ?_, ?_, ?_⟩
  · simpa using η.2.contDiff
  · -- The neighborhood-wise equality to `1` restricts to pointwise equality on `tsupport u`.
    intro x hx
    exact (Filter.EventuallyEq.self_of_nhdsSet hη_one) hx
  · exact hη_zero
  · exact hη_range

/-- Helper for Proposition 8.13: a scalar cutoff equal to `1` on the support of
`u` acts trivially on `u`. -/
lemma eq_smul_of_eqOn_tsupport
    {α : Type*} [TopologicalSpace α]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : α → F} {η : α → ℝ}
    (hη : Set.EqOn η 1 (tsupport u)) :
    u = fun x ↦ η x • u x := by
  funext x
  by_cases hx : x ∈ tsupport u
  · -- On the support, the cutoff is exactly `1`.
    have hηx : η x = 1 := hη hx
    simp [hηx]
  · -- Off the support, the function already vanishes.
    have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hu0]

/-- Helper for Proposition 8.13: multiplying a global approximation by a scalar
cutoff bounded by `1` does not increase the `L¹` approximation error once the
cutoff is `1` on the support of the target function. -/
lemma cutoffRestore_eLpNormOne_le
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : MeasureTheory.Measure α}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u ψ₀ : α → F} {η : α → ℝ}
    (hη_one : Set.EqOn η 1 (tsupport u))
    (hη_norm : ∀ x, |η x| ≤ 1) :
    MeasureTheory.eLpNorm (fun x ↦ u x - η x • ψ₀ x) 1 μ ≤
      MeasureTheory.eLpNorm (fun x ↦ u x - ψ₀ x) 1 μ := by
  -- After rewriting `u = η • u`, compare pointwise using `‖η x‖ ≤ 1`.
  refine MeasureTheory.eLpNorm_mono_ae <| Filter.Eventually.of_forall fun x ↦ ?_
  have hux : u x = η x • u x := by
    simpa using congrFun (eq_smul_of_eqOn_tsupport hη_one) x
  calc
    ‖u x - η x • ψ₀ x‖ = ‖η x • u x - η x • ψ₀ x‖ := by
      exact congrArg (fun z ↦ ‖z - η x • ψ₀ x‖) hux
    _ = ‖η x • (u x - ψ₀ x)‖ := by rw [smul_sub]
    _ ≤ ‖η x‖ * ‖u x - ψ₀ x‖ := norm_smul_le _ _
    _ ≤ ‖u x - ψ₀ x‖ := by
      have hηx : ‖η x‖ ≤ 1 := by
        simpa [Real.norm_eq_abs] using hη_norm x
      nlinarith [norm_nonneg (u x - ψ₀ x)]

end VariationalRegularization
