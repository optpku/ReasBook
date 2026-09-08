module

public import ReasLib.Optimization.DFP.OrthogonalSum

public section

universe u v

/- Infrastructure I.31 (Orthogonal direct-sum lifting of a DFP orbit) (1):
adjoining a zero component, the quadratic complement, and an identity matrix
block transports every certified DFP recurrence to the orthogonal sum. -/
#check (DFP.IsOrbit.orthogonalSum :
  ∀ {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ},
    DFP.IsOrbit f α x g H →
      DFP.IsOrbit (DFP.OrthogonalSum.objective f) α
        (fun k ↦ DFP.OrthogonalSum.embed (x k) :
          ℕ → EuclideanSpace ℝ (ι ⊕ κ))
        (fun k ↦ DFP.OrthogonalSum.embed (g k) :
          ℕ → EuclideanSpace ℝ (ι ⊕ κ))
        (fun k ↦ DFP.OrthogonalSum.matrix (H k) :
          ℕ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ))

/- Infrastructure I.31 (Orthogonal direct-sum lifting of a DFP orbit) (2):
weak Wolfe satisfaction for an embedded step is exactly weak Wolfe satisfaction
in the original summand. -/
#check (LineSearch.IsWeakWolfe.orthogonalSum_iff :
  ∀ {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {c₁ c₂ : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    {x s : EuclideanSpace ℝ ι},
    LineSearch.IsWeakWolfe c₁ c₂ (DFP.OrthogonalSum.objective f)
        (DFP.OrthogonalSum.embed x : EuclideanSpace ℝ (ι ⊕ κ))
        (DFP.OrthogonalSum.embed s : EuclideanSpace ℝ (ι ⊕ κ)) ↔
      LineSearch.IsWeakWolfe c₁ c₂ f x s)
