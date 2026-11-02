module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Pi

open scoped BigOperators

@[expose] public section

section StableSetPolytope

variable {V : Type}
variable (G : SimpleGraph V)

/-- The characteristic vector of a finite stable set, viewed in `ℝ^V`. -/
noncomputable def stableSetIndicator (s : Finset V) : V → ℝ :=
  let _ : DecidableEq V := Classical.decEq V
  fun v ↦ if v ∈ s then 1 else 0

/-- On the support of `s`, `stableSetIndicator s` is `1`. -/
theorem stableSetIndicator_of_mem {s : Finset V} {v : V} (hv : v ∈ s) :
    stableSetIndicator s v = 1 := by
  classical
  simp [stableSetIndicator, hv]

/-- Away from the support of `s`, `stableSetIndicator s` is `0`. -/
theorem stableSetIndicator_of_notMem {s : Finset V} {v : V} (hv : v ∉ s) :
    stableSetIndicator s v = 0 := by
  classical
  simp [stableSetIndicator, hv]

/-- The stable-set vertices are the characteristic vectors of the stable sets of `G`. -/
noncomputable def stableSetVertices : Set (V → ℝ) :=
  {x | ∃ s : Finset V, G.IsIndepSet s ∧ x = stableSetIndicator s}

/-- A point is a stable-set vertex exactly when it is the characteristic vector of a stable set. -/
theorem mem_stableSetVertices_iff {x : V → ℝ} :
    x ∈ stableSetVertices G ↔ ∃ s : Finset V, G.IsIndepSet s ∧ x = stableSetIndicator s :=
  Iff.rfl

/-- The stable set polytope of `G` is the convex hull of its stable-set vertices. -/
noncomputable def stableSetPolytope : Set (V → ℝ) :=
  convexHull ℝ (stableSetVertices G)

/-- Source-facing notation for the stable set polytope of a graph. -/
notation "STAB(" G ")" => stableSetPolytope G

/-- The stable set polytope is defined as the convex hull of `stableSetVertices G`. -/
theorem stableSetPolytope_eq_convexHull :
    STAB(G) = convexHull ℝ (stableSetVertices G) :=
  rfl

/-- Every stable-set indicator belongs to the stable-set polytope. -/
theorem stableSetIndicator_mem_stableSetPolytope {s : Finset V} (hs : G.IsIndepSet s) :
    stableSetIndicator s ∈ STAB(G) := by
  rw [stableSetPolytope_eq_convexHull]
  apply subset_convexHull
  rw [mem_stableSetVertices_iff]
  exact ⟨s, hs, rfl⟩

section CliqueInequalities

private def cliqueLinearMap (K : Finset V) : (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ v ∈ K, LinearMap.proj v

private lemma clique_sum_stableSetIndicator_le_one
    {K s : Finset V} (hK : G.IsClique K) (hs : G.IsIndepSet s) :
    K.sum (fun v ↦ stableSetIndicator s v) ≤ 1 := by
  classical
  have hsum :
      K.sum (fun v ↦ stableSetIndicator s v) = ((K.filter fun v ↦ v ∈ s).card : ℝ) := by
    have hfilter : K.filter (fun v ↦ v ∈ s) = K ∩ s := by
      ext v
      simp
    rw [hfilter]
    simp [stableSetIndicator]
  have hcard : (K.filter fun v ↦ v ∈ s).card ≤ 1 := by
    refine Finset.card_le_one_iff.2 ?_
    intro a b ha hb
    by_contra hab
    have haK : a ∈ K := (Finset.mem_filter.mp ha).1
    have hbK : b ∈ K := (Finset.mem_filter.mp hb).1
    have has : a ∈ s := (Finset.mem_filter.mp ha).2
    have hbs : b ∈ s := (Finset.mem_filter.mp hb).2
    exact (hs has hbs hab) (hK haK hbK hab)
  rw [hsum]
  exact_mod_cast hcard

private lemma clique_sum_le_one_of_mem_stableSetPolytope
    (K : Finset V) (hK : G.IsClique K) (x : V → ℝ) (hx : x ∈ stableSetPolytope G) :
    K.sum x ≤ 1 := by
  let H : Set (V → ℝ) := {y : V → ℝ | K.sum (fun v ↦ y v) ≤ 1}
  have hconvex : Convex ℝ H := by
    simpa [H, cliqueLinearMap, LinearMap.proj_apply] using
      convex_halfSpace_le (cliqueLinearMap K).isLinear (1 : ℝ)
  have hsubset : convexHull ℝ (stableSetVertices G) ⊆ H := by
    refine convexHull_min ?_ hconvex
    intro y hy
    rw [mem_stableSetVertices_iff] at hy
    rcases hy with ⟨s, hs, rfl⟩
    exact clique_sum_stableSetIndicator_le_one G hK hs
  rw [stableSetPolytope_eq_convexHull] at hx
  exact hsubset hx

/-- If `K` is a clique of `G`, then the inequality `∑ j ∈ K, x j ≤ 1` is valid for `STAB(G)`. -/
theorem clique_sum_le_one_on_stableSetPolytope [Finite V]
    (K : Finset V) (hK : G.IsClique K) (x : V → ℝ) (hx : x ∈ stableSetPolytope G) :
    K.sum x ≤ 1 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  exact clique_sum_le_one_of_mem_stableSetPolytope G K hK x hx

end CliqueInequalities

end StableSetPolytope

end
