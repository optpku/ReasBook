/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_27_Local_finiteness_for_shrinking_disjoint_supports_near_a_clos.lean
-/

module

public import ReasLib.Analysis.Calculus.ShrinkingSupportFinsum

public section

open Filter Topology

universe u v

/- Infrastructure I.27 (Local finiteness for shrinking supports near a closed cluster set) (1):
outside `Γ`, every point has a neighborhood meeting only finitely many topological supports.
The result uses only shrinking radii, support containment, and the cluster-point condition. -/
#check (locallyFinite_tsupport_outside :
  ∀ {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F),
    (∀ y, MapClusterPt y atTop x → y ∈ Γ) →
    Tendsto ρ atTop (𝓝 0) →
    (∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k)) →
      ∀ z ∈ Γᶜ, ∃ s ∈ 𝓝 z, {k | (tsupport (ψ k) ∩ s).Nonempty}.Finite)

/- Infrastructure I.27 (Local finiteness for shrinking supports near a closed cluster set) (2):
the pointwise finsum of smooth functions is `C^m` outside `Γ`. -/
#check (contDiffOn_finsum_outside :
  ∀ {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F),
    IsClosed Γ → (∀ y, MapClusterPt y atTop x → y ∈ Γ) →
    Tendsto ρ atTop (𝓝 0) →
    (∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k)) →
    (∀ k, ContDiff ℝ m (ψ k)) → ContDiffOn ℝ m (fun z ↦ ∑ᶠ k, ψ k z) Γᶜ)

/- Infrastructure I.27 (Local finiteness for shrinking supports near a closed cluster set) (3):
at every derivative order, the finsum has the derivative of its active summand outside `Γ`. -/
#check (iteratedFDeriv_finsum_eq_of_mem_tsupport :
  ∀ {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F),
    (∀ y, MapClusterPt y atTop x → y ∈ Γ) →
    Tendsto ρ atTop (𝓝 0) →
    Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)) →
    (∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k)) →
    ∀ {z : E}, z ∈ Γᶜ → ∀ {k j : ℕ}, z ∈ tsupport (ψ k) →
      iteratedFDeriv ℝ j (fun w ↦ ∑ᶠ n, ψ n w) z = iteratedFDeriv ℝ j (ψ k) z)

/- Infrastructure I.27 (Local finiteness for shrinking supports near a closed cluster set) (4):
every derivative of the finsum is zero where no support is active. -/
#check (iteratedFDeriv_finsum_eq_zero :
  ∀ {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F),
    (∀ y, MapClusterPt y atTop x → y ∈ Γ) →
    Tendsto ρ atTop (𝓝 0) →
    (∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k)) →
    ∀ {z : E}, z ∈ Γᶜ → (∀ k, z ∉ tsupport (ψ k)) → ∀ {j : ℕ},
      iteratedFDeriv ℝ j (fun w ↦ ∑ᶠ n, ψ n w) z = 0)
