/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part2

section Chap06
section Section30

/-- Definition 6.30.15: the adjoint `G*` of a concave bifunction `G : ℝ^m → ℝ^n` is the
bifunction on dual variables `x* ∈ ℝ^n` and `u* ∈ ℝ^m` given by
`G*(x*, u*) = sup_{u ∈ ℝ^m, x ∈ ℝ^n} (G(u, x) - ⟪x, x*⟫ + ⟪u, u*⟫)`. Equivalently, for each
`x*`, the slice `G* x*` is the function `u* ↦ sup_{u, x} (G(u, x) - ⟪x, x*⟫ + ⟪u, u*⟫)`. -/
noncomputable def adjointOfConcaveBifunction {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun xStar uStar =>
    sSup (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      G.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)))

/-- The perturbation family of the convex program dual to the concave program associated with
`G`, obtained by passing to the concave adjoint bifunction `G*`. -/
noncomputable abbrev dualPerturbationFunctionOfConcaveProgram {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    (Fin n → ℝ) → EReal :=
  convexProgramAssociatedWith (adjointOfConcaveBifunction G)

-- Proof sketch: view `u ↦ sup_x G(u, x)` as the pointwise supremum of the concave slices induced
-- by the jointly concave bifunction `G`; then apply the convex analogue to the negative function
-- to obtain concavity. For the domain identity, unfold both definitions and note that
-- `(⊥ : EReal) < sup_x G(u, x)` holds exactly when the slice `G u` is not identically `-∞`.
/-- Helper for Theorem 6.30.7: the projection fiber of the negated graph function over `u`
is exactly the range of the negated slice `x ↦ -G(u, x)`. -/
lemma helperForTheorem_6_30_7_projectionFiber_eq_negSliceRange {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G})
    (u : Fin m → ℝ) :
    {z : EReal | ∃ w : Fin (m + n) → ℝ,
      projectionLinearMap (Nat.le_add_right m n) w = u ∧ z = -bifunctionGraphFunction G.1 w} =
      Set.range (fun x : Fin n → ℝ => -G.1 u x) := by
  ext z
  constructor
  · intro hz
    -- Recover the last `n` coordinates of a fiber point and then rebuild the original vector.
    rcases hz with ⟨w, hwproj, rfl⟩
    refine ⟨fun j => w (Fin.natAdd m j), ?_⟩
    have hwproj' := (projectionLinearMap_eq_iff (hmn := Nat.le_add_right m n) w u).1 hwproj
    have hw_eq : w = Fin.append u (fun j => w (Fin.natAdd m j)) := by
      funext i
      cases Nat.lt_or_ge i.1 m with
      | inl hi =>
          have hi' : w i = u ⟨i.1, hi⟩ := hwproj' ⟨i.1, hi⟩
          simpa [Fin.append, Fin.addCases, hi] using hi'
      | inr hi =>
          let j : Fin n := ⟨i.1 - m, by omega⟩
          have hj : Fin.natAdd m j = i := by
            ext
            simp [j]
            omega
          have hji : w (Fin.natAdd m j) = w i := congrArg w hj
          simp [Fin.append, Fin.addCases, hi, hj] at hji ⊢
    rw [hw_eq]
    simp [bifunctionGraphFunction]
  · intro hz
    -- Conversely, append the fixed `u`-coordinates to any slice point `x`.
    rcases hz with ⟨x, rfl⟩
    refine ⟨Fin.append u x, ?_, ?_⟩
    · refine (projectionLinearMap_eq_iff (hmn := Nat.le_add_right m n) _ _).2 ?_
      intro i
      change Fin.append u x ⟨↑i, Nat.lt_of_lt_of_le i.2 (Nat.le_add_right m n)⟩ = u i
      simp [Fin.append, Fin.addCases]
    · simp [bifunctionGraphFunction]

/-- Helper for Theorem 6.30.7: negating the perturbation supremum rewrites it as the fiber
infimum of the negated graph function. -/
lemma helperForTheorem_6_30_7_negPerturbation_eq_sInf_negSlice {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G})
    (u : Fin m → ℝ) :
    -perturbationFunctionOfConcaveProgram G u =
      sInf { z : EReal | ∃ w : Fin (m + n) → ℝ,
        projectionLinearMap (Nat.le_add_right m n) w = u ∧ z = -bifunctionGraphFunction G.1 w } := by
  -- First negate the slice supremum into an infimum over the negated slice values.
  calc
    -perturbationFunctionOfConcaveProgram G u =
        sInf (Set.range fun x : Fin n → ℝ => -G.1 u x) := by
          calc
            -perturbationFunctionOfConcaveProgram G u =
                -(sSup (Set.range fun x : Fin n → ℝ => G.1 u x)) := by
                  rfl
            _ = sInf (Set.range fun x : Fin n → ℝ => -G.1 u x) := by
                  calc
                    -(sSup (Set.range fun x : Fin n → ℝ => G.1 u x)) =
                        -(iSup fun x : Fin n → ℝ => G.1 u x) := by
                          simp [sSup_range]
                    _ = iInf (fun x : Fin n → ℝ => -G.1 u x) := by
                          have h :=
                            helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
                              (φ := fun x : Fin n → ℝ => -G.1 u x)
                          simpa [eq_comm] using congrArg (fun t : EReal => -t) h
                    _ = sInf (Set.range fun x : Fin n → ℝ => -G.1 u x) := by
                          simp [sInf_range]
    -- Then identify the negated slice range with the projection fiber.
    _ = sInf { z : EReal | ∃ w : Fin (m + n) → ℝ,
          projectionLinearMap (Nat.le_add_right m n) w = u ∧ z = -bifunctionGraphFunction G.1 w } := by
        congr 1
        exact (helperForTheorem_6_30_7_projectionFiber_eq_negSliceRange (G := G) u).symm

/-- Helper for Theorem 6.30.7: the negated perturbation function is convex because it is the
fiber-inf image of the convex negated graph function. -/
lemma helperForTheorem_6_30_7_convex_negPerturbation {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    ConvexFunction (n := m) (fun u => -perturbationFunctionOfConcaveProgram G u) := by
  -- Apply the Chapter 1 fiber-inf theorem to the negated graph function.
  have hconvOn :
      ConvexFunctionOn (S := (Set.univ : Set (Fin m → ℝ)))
        (fun u =>
          sInf { z : EReal | ∃ w : Fin (m + n) → ℝ,
            projectionLinearMap (Nat.le_add_right m n) w = u ∧ z = -bifunctionGraphFunction G.1 w }) := by
    simpa using
      (convexFunctionOn_inf_fiber_linearMap
        (A := projectionLinearMap (Nat.le_add_right m n))
        (h := fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w)
        G.2)
  -- Rewrite the fiber-inf function back into the perturbation function.
  have hfun :
      (fun u : Fin m → ℝ =>
        sInf { z : EReal | ∃ w : Fin (m + n) → ℝ,
          projectionLinearMap (Nat.le_add_right m n) w = u ∧ z = -bifunctionGraphFunction G.1 w }) =
      (fun u : Fin m → ℝ => -perturbationFunctionOfConcaveProgram G u) := by
    funext u
    symm
    exact helperForTheorem_6_30_7_negPerturbation_eq_sInf_negSlice (G := G) u
  simpa [ConvexFunction, hfun] using hconvOn

/-- Helper for Theorem 6.30.7: the perturbation value at `u` is above `⊥` exactly when some
point of the slice `G u` is above `⊥`. -/
lemma helperForTheorem_6_30_7_effectiveDomain_mem_iff {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G})
    (u : Fin m → ℝ) :
    ((⊥ : EReal) < perturbationFunctionOfConcaveProgram G u) ↔
      ∃ x : Fin n → ℝ, (⊥ : EReal) < G.1 u x := by
  constructor
  · intro hu
    -- Unfold `⊥ < sSup` into the existence of a slice value strictly above `⊥`.
    rcases (lt_sSup_iff).1 hu with ⟨z, hzmem, hlt⟩
    rcases hzmem with ⟨x, rfl⟩
    exact ⟨x, hlt⟩
  · intro hu
    -- Any witness in the slice gives a lower bound for the supremum defining the perturbation.
    rcases hu with ⟨x, hx⟩
    exact lt_of_lt_of_le hx (le_sSup ⟨x, rfl⟩)

/-- Theorem 6.30.7: if `G` is a concave bifunction from `ℝ^m` to `ℝ^n`, then its perturbation
function `u ↦ sup_{x ∈ ℝ^n} G(u, x)` is a concave extended-real-valued function on `ℝ^m`.
Moreover, the effective domain of this perturbation function is exactly `dom G`, i.e.
`dom (sup G) = dom G`. -/
theorem perturbationFunction_concave_and_effectiveDomain_eq_bifunctionDomain {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    ConvexFunction (n := m) (fun u => -perturbationFunctionOfConcaveProgram G u) ∧
      {u | (⊥ : EReal) < perturbationFunctionOfConcaveProgram G u} =
        concaveBifunctionDomain G := by
  constructor
  · -- The first claim is the convexity of the negated perturbation function.
    exact helperForTheorem_6_30_7_convex_negPerturbation (G := G)
  · -- The effective domains agree because both are characterized by a slice value above `⊥`.
    ext u
    simp [concaveBifunctionDomain, helperForTheorem_6_30_7_effectiveDomain_mem_iff]

end Section30
end Chap06
