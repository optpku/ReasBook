/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section17_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section22_part2

open scoped BigOperators Pointwise
open Topology

section Chap04
section Section22

/-- Helper for Text 22.3.3: pointwise feasibility for the indexed family is exactly
membership in the corresponding range-indexed intersection of half-spaces. -/
lemma helperForText_22_3_3_mem_intersectionOfHalfspaces_iff
    {I : Type*} {n : ℕ} (a : I → (Fin n → ℝ)) (α : I → ℝ) (x : Fin n → ℝ) :
    x ∈ intersectionOfHalfspaces (n := n) (Set.range fun i => (a i, α i)) ↔
      ∀ i, dotProduct (a i) x ≤ α i := by
  constructor
  · intro hx i
    -- Unpack the range-indexed membership and specialize it to the row `(a i, α i)`.
    have hx' : ∀ p ∈ Set.range (fun i => (a i, α i)), x ⬝ᵥ p.1 ≤ p.2 := by
      simpa [intersectionOfHalfspaces] using hx
    simpa [dotProduct_comm] using hx' (a i, α i) ⟨i, rfl⟩
  · intro hx
    -- Conversely, every pointwise inequality supplies the matching half-space condition.
    have hx' : ∀ p ∈ Set.range (fun i => (a i, α i)), x ⬝ᵥ p.1 ≤ p.2 := by
      intro p hp
      rcases hp with ⟨i, rfl⟩
      simpa [dotProduct_comm] using hx i
    simpa [intersectionOfHalfspaces] using hx'

/-- Helper for Text 22.3.3: a finitely supported nonnegative combination of the indexed rows
immediately yields the target consequence inequality. -/
lemma helperForText_22_3_3_finsuppCombination_givesConsequence
    {I : Type*} {n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ)
    (a : I → (Fin n → ℝ)) (α : I → ℝ)
    (l : I →₀ ℝ)
    (hl_nonneg : ∀ i : I, 0 ≤ l i)
    (hsum : l.sum (fun i c => c • a i) = a₀)
    (hscalar : l.sum (fun i c => c * α i) ≤ α₀) :
    ∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ α i) → dotProduct a₀ x ≤ α₀ := by
  intro x hx
  -- Multiply each indexed inequality by its nonnegative coefficient and sum over the support.
  have hweighted :
      Finset.sum l.support (fun i => l i * dotProduct (a i) x) ≤
        Finset.sum l.support (fun i => l i * α i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact mul_le_mul_of_nonneg_left (hx i) (hl_nonneg i)
  have hdot :
      Finset.sum l.support (fun i => l i * dotProduct (a i) x) =
        dotProduct (l.sum (fun i c => c • a i)) x := by
    calc
      Finset.sum l.support (fun i => l i * dotProduct (a i) x)
          = Finset.sum l.support (fun i => dotProduct (l i • a i) x) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [smul_eq_mul]
      _ = dotProduct (Finset.sum l.support (fun i => l i • a i)) x := by
            symm
            simpa using
              (sum_dotProduct (s := l.support) (u := fun i => l i • a i) (v := x))
      _ = dotProduct (l.sum (fun i c => c • a i)) x := by
            rfl
  -- Rewrite the weighted sum using the prescribed coefficient identities.
  calc
    dotProduct a₀ x = dotProduct (l.sum (fun i c => c • a i)) x := by simpa [hsum]
    _ = Finset.sum l.support (fun i => l i * dotProduct (a i) x) := by rw [hdot]
    _ ≤ Finset.sum l.support (fun i => l i * α i) := hweighted
    _ = l.sum (fun i c => c * α i) := rfl
    _ ≤ α₀ := hscalar

/-- Helper for Text 22.3.3: nonempty interior makes the indexed feasible set full-dimensional,
which is the input needed for the finite-subsystem theorem from Section 17. -/
lemma helperForText_22_3_3_fullDim_of_nonemptyInterior
    {I : Type*} {n : ℕ} (a : I → (Fin n → ℝ)) (α : I → ℝ)
    (hinterior : (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ α i}).Nonempty) :
    Module.finrank ℝ
        (affineSpan ℝ
          (intersectionOfHalfspaces (n := n) (Set.range fun i => (a i, α i)))).direction = n := by
  let C : Set (Fin n → ℝ) := {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ α i}
  let Sstar : Set ((Fin n → ℝ) × ℝ) := Set.range fun i => (a i, α i)
  have hCeq : C = intersectionOfHalfspaces (n := n) Sstar := by
    -- Identify the pointwise feasible set with the Section 17 half-space intersection.
    ext x
    simpa [C, Sstar] using (helperForText_22_3_3_mem_intersectionOfHalfspaces_iff a α x).symm
  have hconv : Convex ℝ C := by
    simpa [hCeq] using convex_intersectionOfHalfspaces (n := n) Sstar
  have hspan_top : affineSpan ℝ C = ⊤ :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top (s := C) hconv).1 (by simpa [C] using hinterior)
  have hspan_nonempty : (affineSpan ℝ C : Set (Fin n → ℝ)).Nonempty := by
    simpa [hspan_top] using (Set.univ_nonempty : (Set.univ : Set (Fin n → ℝ)).Nonempty)
  have hdir_top : (affineSpan ℝ C).direction = ⊤ :=
    (AffineSubspace.direction_eq_top_iff_of_nonempty (s := affineSpan ℝ C) hspan_nonempty).2
      hspan_top
  have hfin : Module.finrank ℝ (Fin n → ℝ) = n := by
    calc
      Module.finrank ℝ (Fin n → ℝ) = Fintype.card (Fin n) := by
        exact (Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin n))
      _ = n := by simp
  -- Convert the top-direction statement into the required `finrank = n` statement.
  calc
    Module.finrank ℝ
        (affineSpan ℝ (intersectionOfHalfspaces (n := n) (Set.range fun i => (a i, α i)))).direction =
        Module.finrank ℝ (affineSpan ℝ C).direction := by rw [← hCeq]
    _ =
        Module.finrank ℝ (⊤ : Submodule ℝ (Fin n → ℝ)) := by rw [hdir_top]
    _ = Module.finrank ℝ (Fin n → ℝ) := by simp
    _ = n := hfin

/-- Helper for Text 22.3.3: when the coefficient range avoids the origin, Theorem 17.3.1
extracts `n` indexed inequalities that already imply the target inequality. -/
lemma helperForText_22_3_3_exists_finiteSubsystem_implying_target_of_zeroFreeRange
    {I : Type*} {n : ℕ} {a₀ : Fin n → ℝ} {α₀ : ℝ}
    (ha₀ : a₀ ≠ 0)
    (a : I → (Fin n → ℝ)) (α : I → ℝ)
    (hinterior : (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ α i}).Nonempty)
    (hclosed : IsClosed (Set.range fun i => (a i, α i)))
    (hbounded : Bornology.IsBounded (Set.range fun i => (a i, α i)))
    (hconsequence :
      ∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ α i) → dotProduct a₀ x ≤ α₀)
    (hSstar_ne : (Set.range fun i => (a i, α i)).Nonempty)
    (hSstar0 : (0 : (Fin n → ℝ) × ℝ) ∉ Set.range fun i => (a i, α i)) :
    ∃ idx : Fin n → I,
      ∀ x : Fin n → ℝ,
        (∀ k : Fin n, dotProduct (a (idx k)) x ≤ α (idx k)) → dotProduct a₀ x ≤ α₀ := by
  classical
  let Sstar : Set ((Fin n → ℝ) × ℝ) := Set.range fun i => (a i, α i)
  let r : HalfspaceRep n := ⟨a₀, α₀, ha₀⟩
  have hdim :
      Module.finrank ℝ
          (affineSpan ℝ (intersectionOfHalfspaces (n := n) Sstar)).direction = n :=
    helperForText_22_3_3_fullDim_of_nonemptyInterior a α hinterior
  have hsup : r.set ⊇ intersectionOfHalfspaces (n := n) Sstar := by
    intro x hx
    -- Translate the consequence hypothesis into half-space containment.
    have hxsys : ∀ i, dotProduct (a i) x ≤ α i :=
      (helperForText_22_3_3_mem_intersectionOfHalfspaces_iff a α x).1 (by simpa [Sstar] using hx)
    change x ⬝ᵥ a₀ ≤ α₀
    simpa [r, HalfspaceRep.set, dotProduct_comm] using hconsequence hxsys
  rcases
      (halfspaceRep_set_superset_intersectionOfHalfspaces_iff_exists_fin_n_halfspaces_iInter_subset_page11
        (n := n) (Sstar := Sstar) hSstar_ne hclosed hbounded hSstar0 hdim r).1 hsup with
    ⟨p, hp, hsubset⟩
  choose idx hidx using hp
  refine ⟨idx, ?_⟩
  intro x hx
  have hxmem :
      x ∈ ⋂ i : Fin n, {y : Fin n → ℝ | y ⬝ᵥ (p i).1 ≤ (p i).2} := by
    -- The chosen subsystem inequalities put `x` in the finite intersection from Section 17.
    refine Set.mem_iInter.mpr ?_
    intro i
    have hpi : p i = (a (idx i), α (idx i)) := by
      simpa using (hidx i).symm
    simpa [hpi, dotProduct_comm] using hx i
  have hxhalf : x ∈ r.set := hsubset hxmem
  simpa [r, HalfspaceRep.set, dotProduct_comm] using hxhalf

/-- Helper for Text 22.3.3: finite coefficients on a chosen finite subsystem can be folded
back into a `Finsupp` on the original index type, even if the chosen indices repeat. -/
lemma helperForText_22_3_3_finiteCoeffs_to_finsupp
    {I : Type*} {m n : ℕ}
    (idx : Fin m → I) (lam : Fin m → ℝ)
    (hlam : ∀ k : Fin m, 0 ≤ lam k)
    (a : I → (Fin n → ℝ)) (α : I → ℝ) :
    ∃ l : I →₀ ℝ,
      (∀ i : I, 0 ≤ l i) ∧
        l.sum (fun i c => c • a i) = ∑ k : Fin m, lam k • a (idx k) ∧
          l.sum (fun i c => c * α i) = ∑ k : Fin m, lam k * α (idx k) := by
  classical
  let l : I →₀ ℝ := ∑ k : Fin m, Finsupp.single (idx k) (lam k)
  refine ⟨l, ?_, ?_, ?_⟩
  · intro i
    -- Each packaged coefficient is a finite sum of nonnegative single-index contributions.
    have hterm : ∀ k : Fin m, 0 ≤ (Finsupp.single (idx k) (lam k) : I →₀ ℝ) i := by
      intro k
      by_cases hk : idx k = i
      · simp [hk, hlam]
      · simp [hk]
    simpa [l, Finset.sum_apply] using Finset.sum_nonneg (fun k hk => hterm k)
  · let f : I → ℝ →ₗ[ℝ] (Fin n → ℝ) := fun i => LinearMap.id.smulRight (a i)
    -- View `Finsupp.sum` as a linear map so repeated indices collapse automatically.
    change Finsupp.lsum ℝ f (∑ k : Fin m, Finsupp.single (idx k) (lam k)) = _
    rw [map_sum]
    simp [f]
  · let f : I → ℝ →ₗ[ℝ] ℝ := fun i => LinearMap.id.smulRight (α i)
    -- The scalar right-hand sides package in exactly the same way.
    change Finsupp.lsum ℝ f (∑ k : Fin m, Finsupp.single (idx k) (lam k)) = _
    rw [map_sum]
    simp [f]

/-- Helper for Text 22.3.3: a strict interior point gives strictly positive slack for every
nonzero indexed row. -/
lemma helperForText_22_3_3_positiveSlack_of_nonzeroRow
    {I : Type*} {n : ℕ} (a : I → (Fin n → ℝ)) (α : I → ℝ)
    (hconsistent : ∃ x : Fin n → ℝ, ∀ i, dotProduct (a i) x ≤ α i)
    {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ α i})
    {i : I} (hi : (a i, α i) ≠ 0) :
    0 < α i - dotProduct (a i) xbar := by
  by_cases hai0 : a i = 0
  · rcases hconsistent with ⟨x, hx⟩
    -- When the normal vanishes, consistency forces `α i ≥ 0`; the row being nonzero then
    -- upgrades this to strict positivity.
    have hα_nonneg : 0 ≤ α i := by
      simpa [hai0] using hx i
    have hα_ne : α i ≠ 0 := by
      intro hα0
      apply hi
      ext <;> simp [hai0, hα0]
    have hα_pos : 0 < α i := lt_of_le_of_ne hα_nonneg (by simpa [eq_comm] using hα_ne)
    simpa [hai0] using hα_pos
  ·
    have hsubset :
        {x : Fin n → ℝ | ∀ j, dotProduct (a j) x ≤ α j} ⊆
          {x : Fin n → ℝ | x ⬝ᵥ a i ≤ α i} := by
      intro x hx
      simpa [dotProduct_comm] using hx i
    have hxbar_halfspace : xbar ∈ interior {x : Fin n → ℝ | x ⬝ᵥ a i ≤ α i} :=
      interior_mono hsubset hxbar
    -- The interior-point argument for one half-space supplies the strict inequality.
    have hstrict : dotProduct xbar (a i) < α i :=
      mem_interior_halfspace_le_imp_dot_lt (v := a i) (μ := α i) hai0 hxbar_halfspace
    exact sub_pos.mpr (by simpa [dotProduct_comm] using hstrict)

/-- Helper for Text 22.3.3: the consequence hypothesis puts the target pair in the closure of
the Section 17 cone generated by the indexed coefficient set. -/
lemma helperForText_22_3_3_target_mem_closure_coneK
    {I : Type*} {n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ)
    (a : I → (Fin n → ℝ)) (α : I → ℝ)
    (ha₀ : a₀ ≠ 0)
    (hconsistent : ∃ x : Fin n → ℝ, ∀ i, dotProduct (a i) x ≤ α i)
    (hconsequence :
      ∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ α i) → dotProduct a₀ x ≤ α₀) :
    (a₀, α₀) ∈ closure (coneK (n := n) (Set.range fun i => (a i, α i))) := by
  let Sstar : Set ((Fin n → ℝ) × ℝ) := Set.range fun i => (a i, α i)
  let r : HalfspaceRep n := ⟨a₀, α₀, ha₀⟩
  have hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → ℝ)) := by
    rcases hconsistent with ⟨x, hx⟩
    have hxmem : x ∈ intersectionOfHalfspaces (n := n) Sstar := by
      simpa [Sstar] using (helperForText_22_3_3_mem_intersectionOfHalfspaces_iff a α x).2 hx
    exact Set.nonempty_iff_ne_empty.mp ⟨x, hxmem⟩
  have hsup : r.set ⊇ intersectionOfHalfspaces (n := n) Sstar := by
    intro x hx
    have hxsys : ∀ i, dotProduct (a i) x ≤ α i := by
      simpa [Sstar] using (helperForText_22_3_3_mem_intersectionOfHalfspaces_iff a α x).1 hx
    change x ⬝ᵥ a₀ ≤ α₀
    simpa [r, HalfspaceRep.set, dotProduct_comm] using hconsequence hxsys
  -- Apply the Section 17 support-function argument in its closure form.
  simpa [Sstar, r] using
    (halfspace_contains_intersectionOfHalfspaces_imp_mem_closure_coneK
      (n := n) (Sstar := Sstar) hC_ne r hsup)

/-- Helper for Text 22.3.3: once the target pair lies in `coneK`, the Section 17 conic
representation can be folded into the desired finitely supported certificate. -/
lemma helperForText_22_3_3_finsuppCertificate_of_mem_coneK
    {I : Type*} {n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ)
    (a : I → (Fin n → ℝ)) (α : I → ℝ)
    (hconsistent : ∃ x : Fin n → ℝ, ∀ i, dotProduct (a i) x ≤ α i)
    (hmemK : (a₀, α₀) ∈ coneK (n := n) (Set.range fun i => (a i, α i))) :
    ∃ l : I →₀ ℝ,
      (∀ i, 0 ≤ l i) ∧
        l.sum (fun i c => c • a i) = a₀ ∧
          l.sum (fun i c => c * α i) ≤ α₀ := by
  classical
  let Sstar : Set ((Fin n → ℝ) × ℝ) := Set.range fun i => (a i, α i)
  have hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → ℝ)) := by
    rcases hconsistent with ⟨x, hx⟩
    have hxmem : x ∈ intersectionOfHalfspaces (n := n) Sstar := by
      simpa [Sstar] using (helperForText_22_3_3_mem_intersectionOfHalfspaces_iff a α x).2 hx
    exact Set.nonempty_iff_ne_empty.mp ⟨x, hxmem⟩
  rcases
      mem_coneK_imp_exists_conicCombination_le (n := n) (Sstar := Sstar) (xStar := a₀)
        (muStar := α₀) hC_ne (by simpa [Sstar] using hmemK) with
    ⟨m, hm, p, lam0, lam, hp, hlam0, hlam, hEq⟩
  choose idx hidx using hp
  have hcomponents :
      a₀ = ∑ k, lam k • (p k).1 ∧ α₀ ≥ ∑ k, lam k * (p k).2 :=
    conicCombination_components (n := n) (xStar := a₀) (muStar := α₀) (p := p)
      (lam0 := lam0) (lam := lam) hlam0 hEq
  rcases hcomponents with ⟨ha₀_sum, hα₀_sum⟩
  have hvec :
      a₀ = ∑ k : Fin m, lam k • a (idx k) := by
    calc
      a₀ = ∑ k : Fin m, lam k • (p k).1 := ha₀_sum
      _ = ∑ k : Fin m, lam k • a (idx k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk_eq : p k = (a (idx k), α (idx k)) := by
              simpa using (hidx k).symm
            simpa [hk_eq]
  have hscalar :
      ∑ k : Fin m, lam k * α (idx k) ≤ α₀ := by
    calc
      ∑ k : Fin m, lam k * α (idx k) = ∑ k : Fin m, lam k * (p k).2 := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk_eq : p k = (a (idx k), α (idx k)) := by
              simpa using (hidx k).symm
            simp [hk_eq]
      _ ≤ α₀ := hα₀_sum
  rcases
      helperForText_22_3_3_finiteCoeffs_to_finsupp idx lam hlam a α with
    ⟨l, hl_nonneg, hl_vec, hl_scalar⟩
  refine ⟨l, hl_nonneg, ?_, ?_⟩
  · calc
      l.sum (fun i c => c • a i) = ∑ k : Fin m, lam k • a (idx k) := hl_vec
      _ = a₀ := hvec.symm
  · calc
      l.sum (fun i c => c * α i) = ∑ k : Fin m, lam k * α (idx k) := hl_scalar
      _ ≤ α₀ := hscalar

/-- Helper for Text 22.3.3: for the one-dimensional family `t ↦ (t, t^2)` on `[0, 1]`,
the feasible points are exactly the vectors with nonpositive coordinate. -/
lemma helperForText_22_3_3_counterexample_feasible_iff
    (x : Fin 1 → ℝ) :
    (∀ i : Set.Icc (0 : ℝ) 1, dotProduct (fun _ : Fin 1 => (i : ℝ)) x ≤ (i : ℝ) ^ 2) ↔
      x 0 ≤ 0 := by
  constructor
  · intro hx
    by_contra hxpos
    have hx0_pos : 0 < x 0 := by
      linarith
    let t : ℝ := min (x 0 / 2) 1
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      apply le_min
      · nlinarith
      · norm_num
    have ht_le_one : t ≤ 1 := by
      dsimp [t]
      exact min_le_right _ _
    have ht_pos : 0 < t := by
      -- Choose a positive index `t` small enough to force a contradiction.
      dsimp [t]
      by_cases hx01 : x 0 / 2 ≤ 1
      · rw [min_eq_left hx01]
        nlinarith
      · have h1 : 1 < x 0 / 2 := lt_of_not_ge hx01
        rw [min_eq_right (le_of_lt h1)]
        norm_num
    have ht_lt_x : t < x 0 := by
      -- The same choice also satisfies `t < x 0`, so `t * x 0 ≤ t^2` is impossible.
      dsimp [t]
      by_cases hx01 : x 0 ≤ 1
      · have hhalf_le : x 0 / 2 ≤ 1 := by
          nlinarith
        rw [min_eq_left hhalf_le]
        nlinarith
      · have h1x : 1 < x 0 := lt_of_not_ge hx01
        have hmin_le : min (x 0 / 2) 1 ≤ 1 := min_le_right _ _
        linarith
    have hineq := hx ⟨t, ⟨ht_nonneg, ht_le_one⟩⟩
    have hdiv : x 0 ≤ t := by
      have hdot : dotProduct (fun _ : Fin 1 => t) x = t * x 0 := by
        simp [dotProduct]
      rw [hdot] at hineq
      nlinarith
    linarith
  · intro hx0 i
    -- A nonpositive coordinate automatically satisfies every inequality with `0 ≤ t ≤ 1`.
    have hi_nonneg : 0 ≤ (i : ℝ) := i.2.1
    have hdot : dotProduct (fun _ : Fin 1 => (i : ℝ)) x = (i : ℝ) * x 0 := by
      simp [dotProduct]
    rw [hdot]
    have hmul_nonpos : (i : ℝ) * x 0 ≤ 0 := by
      nlinarith
    have hi_sq_nonneg : 0 ≤ (i : ℝ) ^ 2 := sq_nonneg _
    linarith

/-- Helper for Text 22.3.3: the family `t ↦ (t, t^2)` on `[0, 1]` admits no finitely
supported nonnegative certificate for the target pair `(1, 0)`. -/
lemma helperForText_22_3_3_counterexample_no_finite_certificate :
    ¬ ∃ l : Set.Icc (0 : ℝ) 1 →₀ ℝ,
      (∀ i, 0 ≤ l i) ∧
        l.sum (fun i c => c • (fun _ : Fin 1 => (i : ℝ))) = (fun _ : Fin 1 => (1 : ℝ)) ∧
          l.sum (fun i c => c * (i : ℝ) ^ 2) ≤ 0 := by
  rintro ⟨l, hl_nonneg, hvec, hscalar⟩
  have hcoord : l.sum (fun i c => c * (i : ℝ)) = (1 : ℝ) := by
    -- Reading the vector identity in the unique coordinate gives `sum c_i * t_i = 1`.
    have h0 := congrArg (fun v : Fin 1 → ℝ => v 0) hvec
    simpa [Finsupp.sum, smul_eq_mul] using h0
  have hcoord_ne : l.sum (fun i c => c * (i : ℝ)) ≠ 0 := by
    rw [hcoord]
    norm_num
  have hsum_ne : Finset.sum l.support (fun i => l i * (i : ℝ)) ≠ 0 := by
    simpa [Finsupp.sum] using hcoord_ne
  rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_ne with ⟨i, hi_support, hprod_ne⟩
  have hprod_nonneg : 0 ≤ l i * (i : ℝ) := by
    have hi_nonneg : 0 ≤ (i : ℝ) := i.2.1
    nlinarith [hl_nonneg i, hi_nonneg]
  have hprod_pos : 0 < l i * (i : ℝ) := by
    have hprod_eq : l i * (i : ℝ) ≠ 0 := hprod_ne
    exact lt_of_le_of_ne hprod_nonneg (by symm; exact hprod_eq)
  have hsq_pos : 0 < l i * (i : ℝ) ^ 2 := by
    -- One positive term in the linear combination forces a positive scalar contribution.
    have hi_nonneg : 0 ≤ (i : ℝ) := i.2.1
    nlinarith [hl_nonneg i, hi_nonneg, hprod_pos]
  have hterm_nonneg : ∀ j ∈ l.support, 0 ≤ l j * (j : ℝ) ^ 2 := by
    intro j hj
    have hj_nonneg : 0 ≤ (j : ℝ) := j.2.1
    nlinarith [hl_nonneg j, hj_nonneg]
  have hle_sum : l i * (i : ℝ) ^ 2 ≤ Finset.sum l.support (fun j => l j * (j : ℝ) ^ 2) := by
    exact Finset.single_le_sum hterm_nonneg hi_support
  have hsum_pos : 0 < l.sum (fun j c => c * (j : ℝ) ^ 2) := by
    exact lt_of_lt_of_le hsq_pos hle_sum
  linarith

/-- Helper for Text 22.3.3: the compact family `t ↦ (t, t^2)` on `[0, 1]` satisfies the
theorem hypotheses and makes the textbook biconditional fail. -/
lemma helperForText_22_3_3_exists_counterexample_to_schema :
    ∃ (I : Type) (a₀ : Fin 1 → ℝ) (α₀ : ℝ) (a : I → (Fin 1 → ℝ)) (α : I → ℝ),
      (∃ x : Fin 1 → ℝ, ∀ i, dotProduct (a i) x ≤ α i) ∧
        (interior {x : Fin 1 → ℝ | ∀ i, dotProduct (a i) x ≤ α i}).Nonempty ∧
        IsClosed (Set.range fun i => (a i, α i)) ∧
        Bornology.IsBounded (Set.range fun i => (a i, α i)) ∧
        (∀ ⦃x : Fin 1 → ℝ⦄, (∀ i, dotProduct (a i) x ≤ α i) → dotProduct a₀ x ≤ α₀) ∧
        ¬ ∃ l : I →₀ ℝ,
          (∀ i, 0 ≤ l i) ∧
            l.sum (fun i c => c • a i) = a₀ ∧
              l.sum (fun i c => c * α i) ≤ α₀ := by
  refine ⟨Set.Icc (0 : ℝ) 1, (fun _ : Fin 1 => (1 : ℝ)), 0,
    (fun i _ => (i : ℝ)), (fun i => (i : ℝ) ^ 2), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨0, ?_⟩
    intro i
    -- The zero vector is feasible because every right-hand side is nonnegative.
    have hi_sq_nonneg : 0 ≤ (i : ℝ) ^ 2 := sq_nonneg _
    simp [dotProduct, hi_sq_nonneg]
  · let U : Set (Fin 1 → ℝ) := {x : Fin 1 → ℝ | x 0 < 0}
    let xbar : Fin 1 → ℝ := fun _ => (-1 : ℝ)
    have hU_open : IsOpen U := by
      simpa [U] using isOpen_lt (continuous_apply 0) continuous_const
    have hxbar_mem : xbar ∈ U := by
      simp [U, xbar]
    have hU_subset : U ⊆ {x : Fin 1 → ℝ | ∀ i : Set.Icc (0 : ℝ) 1,
        dotProduct (fun _ : Fin 1 => (i : ℝ)) x ≤ (i : ℝ) ^ 2} := by
      intro x hxU
      have hx0 : x 0 ≤ 0 := by
        linarith [show x 0 < 0 from hxU]
      exact (helperForText_22_3_3_counterexample_feasible_iff x).2 hx0
    -- The open negative half-line sits inside the feasible set, so the feasible set
    -- has nonempty interior.
    refine ⟨xbar, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset (hU_open.mem_nhds hxbar_mem) hU_subset
  · let g : ℝ → ((Fin 1 → ℝ) × ℝ) := fun t => ((fun _ : Fin 1 => t), t ^ 2)
    have hrange :
        Set.range (fun i : Set.Icc (0 : ℝ) 1 => ((fun _ : Fin 1 => (i : ℝ)), (i : ℝ) ^ 2)) =
          g '' Set.Icc (0 : ℝ) 1 := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩
    have hcont : Continuous g := by
      continuity
    have hcompact : IsCompact (g '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image hcont
    -- Closedness follows because the coefficient set is a compact interval image.
    simpa [hrange] using hcompact.isClosed
  · let g : ℝ → ((Fin 1 → ℝ) × ℝ) := fun t => ((fun _ : Fin 1 => t), t ^ 2)
    have hrange :
        Set.range (fun i : Set.Icc (0 : ℝ) 1 => ((fun _ : Fin 1 => (i : ℝ)), (i : ℝ) ^ 2)) =
          g '' Set.Icc (0 : ℝ) 1 := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩
    have hcont : Continuous g := by
      continuity
    have hcompact : IsCompact (g '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image hcont
    -- The same compactness argument supplies boundedness.
    simpa [hrange] using hcompact.isBounded
  · intro x hx
    -- The feasible set is exactly `{x | x 0 ≤ 0}`, so the target inequality is valid.
    have hx0 : x 0 ≤ 0 := (helperForText_22_3_3_counterexample_feasible_iff x).1 hx
    simpa [dotProduct] using hx0
  · simpa using helperForText_22_3_3_counterexample_no_finite_certificate

/-- Helper for Text 22.3.3: the compact family `t ↦ (t, t^2)` already satisfies the extra
`a₀ ≠ 0`, nonempty-range, and `0 ∈ range` hypotheses from the blocked branch, while still
admitting no finite certificate. -/
lemma helperForText_22_3_3_exists_counterexample_to_origin_range_branch :
    ∃ (a₀ : Fin 1 → ℝ) (α₀ : ℝ)
      (a : Set.Icc (0 : ℝ) 1 → (Fin 1 → ℝ)) (α : Set.Icc (0 : ℝ) 1 → ℝ),
      a₀ ≠ 0 ∧
        (∃ x : Fin 1 → ℝ, ∀ i, dotProduct (a i) x ≤ α i) ∧
        (interior {x : Fin 1 → ℝ | ∀ i, dotProduct (a i) x ≤ α i}).Nonempty ∧
        IsClosed (Set.range fun i => (a i, α i)) ∧
        Bornology.IsBounded (Set.range fun i => (a i, α i)) ∧
        (∀ ⦃x : Fin 1 → ℝ⦄, (∀ i, dotProduct (a i) x ≤ α i) → dotProduct a₀ x ≤ α₀) ∧
        (Set.range fun i => (a i, α i)).Nonempty ∧
        ((0 : (Fin 1 → ℝ) × ℝ) ∈ Set.range fun i => (a i, α i)) ∧
        ¬ ∃ l : Set.Icc (0 : ℝ) 1 →₀ ℝ,
          (∀ i, 0 ≤ l i) ∧
            l.sum (fun i c => c • a i) = a₀ ∧
              l.sum (fun i c => c * α i) ≤ α₀ := by
  have hzero_in_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    -- The parameter value `t = 0` lies in the compact index interval.
    constructor <;> norm_num
  let i0 : Set.Icc (0 : ℝ) 1 := ⟨0, hzero_in_Icc⟩
  have hzero_mem :
      (0 : (Fin 1 → ℝ) × ℝ) ∈
        Set.range (fun i : Set.Icc (0 : ℝ) 1 => ((fun _ : Fin 1 => (i : ℝ)), (i : ℝ) ^ 2)) := by
    -- Evaluating the counterexample family at `t = 0` yields the origin.
    refine ⟨i0, ?_⟩
    ext <;> simp [i0]
  refine ⟨(fun _ : Fin 1 => (1 : ℝ)), 0,
    (fun (i : Set.Icc (0 : ℝ) 1) (_ : Fin 1) => (i : ℝ)),
    (fun i => (i : ℝ) ^ 2), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hzero_mem, ?_⟩
  · -- Read the target vector in its unique coordinate to see it is nonzero.
    intro hzero
    have hcoord := congrArg (fun v : Fin 1 → ℝ => v 0) hzero
    norm_num at hcoord
  · refine ⟨0, ?_⟩
    intro i
    -- The zero vector is feasible because each right-hand side is nonnegative.
    have hi_sq_nonneg : 0 ≤ (i : ℝ) ^ 2 := sq_nonneg _
    simp [dotProduct, hi_sq_nonneg]
  · let U : Set (Fin 1 → ℝ) := {x : Fin 1 → ℝ | x 0 < 0}
    let xbar : Fin 1 → ℝ := fun _ => (-1 : ℝ)
    have hU_open : IsOpen U := by
      simpa [U] using isOpen_lt (continuous_apply 0) continuous_const
    have hxbar_mem : xbar ∈ U := by
      simp [U, xbar]
    have hU_subset : U ⊆ {x : Fin 1 → ℝ |
        ∀ i : Set.Icc (0 : ℝ) 1, dotProduct (fun _ : Fin 1 => (i : ℝ)) x ≤ (i : ℝ) ^ 2} := by
      intro x hxU
      have hx0 : x 0 ≤ 0 := by
        linarith [show x 0 < 0 from hxU]
      exact (helperForText_22_3_3_counterexample_feasible_iff x).2 hx0
    -- The open negative half-line sits inside the feasible set.
    refine ⟨xbar, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset (hU_open.mem_nhds hxbar_mem) hU_subset
  · let g : ℝ → ((Fin 1 → ℝ) × ℝ) := fun t => ((fun _ : Fin 1 => t), t ^ 2)
    have hrange :
        Set.range (fun i : Set.Icc (0 : ℝ) 1 => ((fun _ : Fin 1 => (i : ℝ)), (i : ℝ) ^ 2)) =
          g '' Set.Icc (0 : ℝ) 1 := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩
    have hcont : Continuous g := by
      continuity
    have hcompact : IsCompact (g '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image hcont
    -- Closedness follows because the coefficient set is a compact interval image.
    simpa [hrange] using hcompact.isClosed
  · let g : ℝ → ((Fin 1 → ℝ) × ℝ) := fun t => ((fun _ : Fin 1 => t), t ^ 2)
    have hrange :
        Set.range (fun i : Set.Icc (0 : ℝ) 1 => ((fun _ : Fin 1 => (i : ℝ)), (i : ℝ) ^ 2)) =
          g '' Set.Icc (0 : ℝ) 1 := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩
    have hcont : Continuous g := by
      continuity
    have hcompact : IsCompact (g '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image hcont
    -- The same compactness argument gives boundedness.
    simpa [hrange] using hcompact.isBounded
  · intro x hx
    -- The feasible set is exactly `{x | x 0 ≤ 0}` for the counterexample family.
    have hx0 : x 0 ≤ 0 := (helperForText_22_3_3_counterexample_feasible_iff x).1 hx
    simpa [dotProduct] using hx0
  · -- Nonemptiness follows from the origin witness already lying in the range.
    exact ⟨0, hzero_mem⟩
  · simpa using helperForText_22_3_3_counterexample_no_finite_certificate

/-- Helper for Text 22.3.3: the `0 ∈ range` branch is false as stated; the compact family
`t ↦ (t, t^2)` on `[0, 1]` gives a direct counterexample to any universal forward-certificate
claim in that branch. -/
lemma helperForText_22_3_3_origin_mem_range_forward_certificate
    :
    ¬ (
      ∀ {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ)
        (a : I → (Fin n → ℝ)) (α : I → ℝ),
        a₀ ≠ 0 →
          (∃ x : Fin n → ℝ, ∀ i, dotProduct (a i) x ≤ α i) →
            (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ α i}).Nonempty →
              IsClosed (Set.range fun i => (a i, α i)) →
                Bornology.IsBounded (Set.range fun i => (a i, α i)) →
                  (∀ ⦃x : Fin n → ℝ⦄,
                    (∀ i, dotProduct (a i) x ≤ α i) → dotProduct a₀ x ≤ α₀) →
                    (Set.range fun i => (a i, α i)).Nonempty →
                      ((0 : (Fin n → ℝ) × ℝ) ∈ Set.range fun i => (a i, α i)) →
                        ∃ l : I →₀ ℝ,
                          (∀ i, 0 ≤ l i) ∧
                            l.sum (fun i c => c • a i) = a₀ ∧
                              l.sum (fun i c => c * α i) ≤ α₀
    ) := by
  intro hbranch
  -- Instantiate the claimed universal branch principle with the explicit compact
  -- counterexample already constructed in the file.
  rcases helperForText_22_3_3_exists_counterexample_to_origin_range_branch with
    ⟨a₀, α₀, a, α, ha₀, hconsistent, hinterior, hclosed, hbounded, hconsequence,
      hSstar_ne, hzero_mem, hnoCert⟩
  exact
    hnoCert
      (hbranch a₀ α₀ a α ha₀ hconsistent hinterior hclosed hbounded hconsequence
        hSstar_ne hzero_mem)

/- Helper for Text 22.3.3: when the target normal vanishes, the forward implication is
witnessed by the zero `Finsupp` once consistency shows `0 ≤ α₀`. -/
lemma helperForText_22_3_3_zeroNormal_forward_certificate
    {I : Type*} {n : ℕ} (α₀ : ℝ)
    (a : I → (Fin n → ℝ)) (α : I → ℝ)
    (hconsistent : ∃ x : Fin n → ℝ, ∀ i, dotProduct (a i) x ≤ α i)
    (hconsequence :
      ∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ α i) → dotProduct (0 : Fin n → ℝ) x ≤ α₀) :
    ∃ l : I →₀ ℝ,
      (∀ i, 0 ≤ l i) ∧
        l.sum (fun i c => c • a i) = (0 : Fin n → ℝ) ∧
          l.sum (fun i c => c * α i) ≤ α₀ := by
  rcases hconsistent with ⟨x, hx⟩
  have hα₀ : 0 ≤ α₀ := by
    -- Evaluating the consequence at one feasible point forces the scalar bound.
    simpa using hconsequence hx
  refine ⟨0, ?_, ?_, ?_⟩
  · intro i
    simp
  · simp
  · simpa using hα₀

-- Proof sketch: apply the infinite-system Farkas theorem under the hypotheses that the
-- feasible set has nonempty interior and the coefficient set is closed and bounded. The
-- resulting dual certificate can be chosen with finite support, which is encoded by a
-- finitely supported nonnegative multiplier function `l : I →₀ ℝ`.
/-- Text 22.3.3: Let `I` be an index set and let `(aᵢ, αᵢ) ∈ ℝⁿ × ℝ` for each `i ∈ I`.
Assume the system `⟪aᵢ, x⟫ ≤ αᵢ` is consistent, its solution set
`{x ∈ ℝⁿ | ⟪aᵢ, x⟫ ≤ αᵢ for all i ∈ I}` has nonempty interior, the coefficient set
`{(aᵢ, αᵢ) | i ∈ I}` is closed and bounded in `ℝⁿ × ℝ`, and the origin does not occur among
those coefficient pairs. Then the consequence relation for `⟪a₀, x⟫ ≤ α₀` is equivalent to
the existence of a finite nonnegative combination of the given inequalities yielding `a₀`
with right-hand side at most `α₀`, encoded by a finitely supported multiplier
`l : I →₀ ℝ`. -/
theorem indexedLinearInequality_isConsequence_iff_finite_nonnegative_combination
    {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ)
    (a : I → (Fin n → ℝ)) (α : I → ℝ)
    (hconsistent : ∃ x : Fin n → ℝ, ∀ i, dotProduct (a i) x ≤ α i)
    (hinterior : (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ α i}).Nonempty)
    (hclosed : IsClosed (Set.range fun i => (a i, α i)))
    (hbounded : Bornology.IsBounded (Set.range fun i => (a i, α i)))
    (hzeroFree : (0 : (Fin n → ℝ) × ℝ) ∉ Set.range fun i => (a i, α i)) :
    (∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ α i) → dotProduct a₀ x ≤ α₀) ↔
      ∃ l : I →₀ ℝ,
        (∀ i, 0 ≤ l i) ∧
          l.sum (fun i c => c • a i) = a₀ ∧
          l.sum (fun i c => c * α i) ≤ α₀ := by
  constructor
  · intro hconsequence
    by_cases hzero : a₀ = 0
    · -- The zero-normal branch collapses to the scalar inequality `0 ≤ α₀`.
      have hzeroConsequence :
          ∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ α i) →
            dotProduct (0 : Fin n → ℝ) x ≤ α₀ := by
        simpa [hzero] using hconsequence
      simpa [hzero] using
        helperForText_22_3_3_zeroNormal_forward_certificate α₀ a α hconsistent hzeroConsequence
    · have ha₀ : a₀ ≠ 0 := hzero
      by_cases hSstar_ne : (Set.range fun i => (a i, α i)).Nonempty
      · rcases
          helperForText_22_3_3_exists_finiteSubsystem_implying_target_of_zeroFreeRange
            ha₀ a α hinterior hclosed hbounded hconsequence hSstar_ne hzeroFree with
          ⟨idx, hidxConsequence⟩
        have hconsistent_fin :
            ∃ x : Fin n → ℝ, ∀ k : Fin n, dotProduct (a (idx k)) x ≤ α (idx k) := by
          rcases hconsistent with ⟨x, hx⟩
          exact ⟨x, fun k => hx (idx k)⟩
        have hfiniteCert :
            ∃ lam : Fin n → ℝ, 0 ≤ lam ∧
              (∑ k, lam k • a (idx k)) = a₀ ∧
                (∑ k, lam k * α (idx k)) ≤ α₀ := by
          exact
            (linearInequality_isConsequence_iff_nonnegative_combination
              a₀ α₀ (fun k => a (idx k)) (fun k => α (idx k)) hconsistent_fin).1 hidxConsequence
        rcases hfiniteCert with ⟨lam, hlam, hvec, hscalar⟩
        rcases
            helperForText_22_3_3_finiteCoeffs_to_finsupp idx lam
              (fun k => hlam k) a α with
          ⟨l, hl_nonneg, hl_vec, hl_scalar⟩
        refine ⟨l, hl_nonneg, ?_, ?_⟩
        · simpa [hvec] using hl_vec
        · calc
            l.sum (fun i c => c * α i) = ∑ k : Fin n, lam k * α (idx k) := hl_scalar
            _ ≤ α₀ := hscalar
      · have hIempty : IsEmpty I := ⟨fun i => hSstar_ne ⟨(a i, α i), ⟨i, rfl⟩⟩⟩
        letI : IsEmpty I := hIempty
        let x : Fin n → ℝ := ((α₀ + 1) / dotProduct a₀ a₀) • a₀
        have hself_ne : dotProduct a₀ a₀ ≠ 0 := by
          intro hself_zero
          exact ha₀ ((dotProduct_self_eq_zero (v := a₀)).1 hself_zero)
        have hfeasible : ∀ i, dotProduct (a i) x ≤ α i := by
          intro i
          exact (isEmptyElim i)
        have hx_value : dotProduct a₀ x = α₀ + 1 := by
          -- With no system inequalities at all, the feasible set is all of `ℝⁿ`; use a point
          -- that violates the claimed consequence.
          calc
            dotProduct a₀ x = ((α₀ + 1) / dotProduct a₀ a₀) * dotProduct a₀ a₀ := by
              simp [x]
            _ = α₀ + 1 := by
              field_simp [hself_ne]
        have hbad : False := by
          have hx_le : dotProduct a₀ x ≤ α₀ := hconsequence hfeasible
          rw [hx_value] at hx_le
          linarith
        exact False.elim hbad
  · rintro ⟨l, hl_nonneg, hsum, hscalar⟩
    -- The reverse implication is the direct weighted-sum argument over the finite support.
    exact
      helperForText_22_3_3_finsuppCombination_givesConsequence
        a₀ α₀ a α l hl_nonneg hsum hscalar

end Section22
end Chap04
