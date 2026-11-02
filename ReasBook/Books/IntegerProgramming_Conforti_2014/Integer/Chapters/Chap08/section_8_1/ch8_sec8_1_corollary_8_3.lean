import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

-- Semantic theorem search via `lean_leansearch` was unavailable in this environment, so this file
-- uses mathlib's canonical `AffineMap` and `ConvexOn` APIs for the finite-affine-maximum model
-- behind Corollary 8.3.

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Corollary83

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {ι : Type v}
variable {domain : Set E} {zLR : E → ℝ} {branches : Finset ι}
variable {affineBranch : ι → E →ᵃ[ℝ] ℝ}

private theorem affine_branch_convexOn
    (hdomain : Convex ℝ domain) (i : ι) :
    ConvexOn ℝ domain (affineBranch i) := by
  have hid : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ ↦ x) := convexOn_id convex_univ
  simpa using (hid.comp_affineMap (affineBranch i)).subset (by simp) hdomain

private theorem convexOn_sup'_affine_branch
    (hdomain : Convex ℝ domain) (hbranches : branches.Nonempty) :
    ConvexOn ℝ domain (fun x ↦ branches.sup' hbranches (fun i ↦ affineBranch i x)) := by
  classical
  induction hbranches using Finset.Nonempty.cons_induction with
  | singleton i =>
      simpa using affine_branch_convexOn hdomain i
  | cons i s his hs ih =>
      have hsup :
          ConvexOn ℝ domain
            (fun x ↦ max (affineBranch i x) (s.sup' hs (fun j ↦ affineBranch j x))) := by
        simpa using (affine_branch_convexOn hdomain i).sup ih
      refine hsup.congr fun x hx ↦ ?_
      have hcons :
          (Finset.cons i s his).sup' (Finset.cons_nonempty his) (fun j ↦ affineBranch j x) =
            max (affineBranch i x) (s.sup' hs (fun j ↦ affineBranch j x)) := by
        simpa using
          (show
            (Finset.cons i s his).sup' (Finset.cons_nonempty his) (fun j ↦ affineBranch j x) =
              (fun j ↦ affineBranch j x) i ⊔ s.sup' hs (fun j ↦ affineBranch j x)
            from Finset.sup'_cons hs (fun j ↦ affineBranch j x))
      exact hcons.symm

section FiniteAffineMaximum

variable (hbranches : branches.Nonempty)
variable (hmax : ∀ x ∈ domain, zLR x = branches.sup' hbranches (fun i ↦ affineBranch i x))

include hbranches hmax

/-- Corollary 8.3 (1) in pointwise form: if `z_LR` is represented on `domain` as the maximum of
finitely many affine branches, then at each chosen `x ∈ domain` one branch is active and
dominates all the others there. -/
theorem z_lr_piecewise_linear_at
    {x : E} (hx : x ∈ domain) :
    ∃ i ∈ branches, zLR x = affineBranch i x ∧
      ∀ j ∈ branches, affineBranch j x ≤ affineBranch i x := by
  obtain ⟨i, hi, hsup⟩ := branches.exists_mem_eq_sup' hbranches (fun j ↦ affineBranch j x)
  refine ⟨i, hi, ?_, ?_⟩
  · calc
      zLR x = branches.sup' hbranches (fun j ↦ affineBranch j x) := hmax x hx
      _ = affineBranch i x := hsup
  · intro j hj
    rw [← hsup]
    exact Finset.le_sup' (fun k ↦ affineBranch k x) hj

/-- Corollary 8.3 (1). If `z_LR` is given on its domain by the maximum of finitely many affine
functions as in `(8.4)`, then on each point of the domain it agrees with an active affine branch;
this is the piecewise-linear part of the corollary. -/
theorem z_lr_piecewise_linear_on_domain
    : ∀ x ∈ domain, ∃ i ∈ branches, zLR x = affineBranch i x ∧
      ∀ j ∈ branches, affineBranch j x ≤ affineBranch i x := by
  intro x hx
  exact z_lr_piecewise_linear_at hbranches hmax hx

/-- Corollary 8.3 (2). Over its convex domain, the Lagrangian-relaxation value function `z_LR`
is convex in `λ` whenever it is represented there as the maximum of finitely many affine
functions. -/
theorem z_lr_convex_on_domain
    (hdomain : Convex ℝ domain) :
    ConvexOn ℝ domain zLR :=
  (convexOn_sup'_affine_branch hdomain hbranches).congr fun x hx ↦ (hmax x hx).symm

omit hbranches hmax

end FiniteAffineMaximum

end Corollary83
