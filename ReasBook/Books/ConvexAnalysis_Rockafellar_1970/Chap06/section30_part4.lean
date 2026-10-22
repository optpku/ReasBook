/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part3

section Chap06
section Section30

-- Proof sketch: expand the Kuhn--Tucker condition from Definition 6.30.12 with
-- `h = sup G`, rewrite the common supremum as the Fenchel conjugate of `fun u => -h u`
-- evaluated at `uStar`, and then apply the Chapter 6 subgradient characterization for equality
-- in the Fenchel--Young inequality at `u = 0`. The resulting criterion is exactly finiteness of
-- `h 0` together with `-uStar ∈ ∂h(0)`.
/-- Helper for Theorem 6.30.8: the pairwise Kuhn--Tucker supremum is the perturbation-function
supremum after collapsing each fiber over `u`. -/
lemma helperForTheorem_6_30_8_bifunctionSup_eq_perturbationSup {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G})
    (uStar : Fin m → ℝ) :
    sSup (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      (((uStar ⬝ᵥ p.1 : ℝ) : EReal) + G.1 p.1 p.2)) =
      sSup (Set.range fun u : Fin m → ℝ =>
        (((uStar ⬝ᵥ u : ℝ) : EReal) + perturbationFunctionOfConcaveProgram G u)) := by
  let g : (Fin m → ℝ) × (Fin n → ℝ) → EReal :=
    fun p => (((uStar ⬝ᵥ p.1 : ℝ) : EReal) + G.1 p.1 p.2)
  -- Collapse the total supremum to the supremum of the fibers indexed by `u`.
  have hcollapse :=
    section16_sSup_range_sSup_fiber_image_eq_sSup_range_total (A := Prod.fst) (g := g)
  have hfiber :
      (fun u : Fin m → ℝ =>
        sSup ((fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          (((uStar ⬝ᵥ p.1 : ℝ) : EReal) + G.1 p.1 p.2)) '' {p | Prod.fst p = u})) =
      (fun u : Fin m → ℝ => (((uStar ⬝ᵥ u : ℝ) : EReal) + perturbationFunctionOfConcaveProgram G u)) := by
    funext u
    -- Rewrite the fiber over `u` as the range of the corresponding `x`-slice.
    have hsset :
        ((fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          (((uStar ⬝ᵥ p.1 : ℝ) : EReal) + G.1 p.1 p.2)) '' {p | Prod.fst p = u}) =
        Set.range (fun x : Fin n → ℝ => (((uStar ⬝ᵥ u : ℝ) : EReal) + G.1 u x)) := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        rcases p with ⟨u', x⟩
        simp at hp
        rcases hp with rfl
        exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨⟨u, x⟩, rfl, rfl⟩
    rw [hsset]
    -- Move the fixed affine term outside the slice supremum.
    have himage :
        Set.range (fun x : Fin n → ℝ => (((uStar ⬝ᵥ u : ℝ) : EReal) + G.1 u x)) =
        ((fun z : EReal => z + (((uStar ⬝ᵥ u : ℝ) : EReal))) ''
          Set.range (fun x : Fin n → ℝ => G.1 u x)) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨G.1 u x, ⟨x, rfl⟩, ?_⟩
        simp [add_comm]
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, by simp [add_comm]⟩
    rw [himage,
      section13_sSup_image_add_right (c := uStar ⬝ᵥ u)
        (s := Set.range fun x : Fin n → ℝ => G.1 u x)]
    simp [perturbationFunctionOfConcaveProgram, concaveProgramAssociatedWith, add_comm]
  calc
    sSup (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      (((uStar ⬝ᵥ p.1 : ℝ) : EReal) + G.1 p.1 p.2)) =
        sSup (Set.range fun u : Fin m → ℝ =>
          sSup ((fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
            (((uStar ⬝ᵥ p.1 : ℝ) : EReal) + G.1 p.1 p.2)) '' {p | Prod.fst p = u})) := by
          simpa [g] using hcollapse.symm
    _ = sSup (Set.range fun u : Fin m → ℝ =>
        (((uStar ⬝ᵥ u : ℝ) : EReal) + perturbationFunctionOfConcaveProgram G u)) := by
          simp [hfiber]

/-- Helper for Theorem 6.30.8: membership in the concave subdifferential at the origin is the
supporting-hyperplane inequality written with the perturbation function. -/
lemma helperForTheorem_6_30_8_neg_mem_concaveSubdifferentialAt_zero_iff_supporting_inequality
    {m : ℕ} (h : (Fin m → ℝ) → EReal) (uStar : Fin m → ℝ) :
    (-uStar) ∈ concaveSubdifferentialAt h 0 ↔
      ∀ u : Fin m → ℝ, (((uStar ⬝ᵥ u : ℝ) : EReal) + h u) ≤ h 0 := by
  constructor
  · intro hu u
    -- Unfold the subgradient condition for the convex function `-h` at the origin.
    have hineq' : IsSubgradientAt (fun z => -h z) 0 (dotProductEquiv ℝ (Fin m) uStar) := by
      simpa [concaveSubdifferentialAt, IsEuclideanSubgradientAt, subdifferentialAt] using hu
    have hineq := hineq' u
    let a : EReal := (((uStar ⬝ᵥ u : ℝ) : EReal))
    have hle_sub : h u ≤ h 0 - a := by
      have hraw : -h 0 + a ≤ -h u := by
        simpa [a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hineq
      have hneg : h u ≤ -(a + -h 0) := by
        simpa [a, add_comm, add_left_comm, add_assoc] using (EReal.le_neg).2 hraw
      have hneg_add : -(a + -h 0) = -a + h 0 := by
        have ha_bot : a ≠ (⊥ : EReal) := by simp [a]
        have ha_top : a ≠ (⊤ : EReal) := by simp [a]
        calc
          -(a + -h 0) = -a - (-h 0) :=
            EReal.neg_add (Or.inl ha_bot) (Or.inl ha_top)
          _ = -a + h 0 := by simp [sub_eq_add_neg]
      rw [hneg_add] at hneg
      simpa [a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    have h1 : a ≠ (⊥ : EReal) ∨ h 0 ≠ (⊥ : EReal) := Or.inl (by simp [a])
    have h2 : a ≠ (⊤ : EReal) ∨ h 0 ≠ (⊤ : EReal) := Or.inl (by simp [a])
    have hadd_le : h u + a ≤ h 0 :=
      (EReal.le_sub_iff_add_le (a := h u) (b := a) (c := h 0) h1 h2).1 hle_sub
    simpa [a, add_comm, add_left_comm, add_assoc] using hadd_le
  · intro hu
    -- Repackage the supporting inequality as the defining subgradient inequality at `0`.
    have hineq' : IsSubgradientAt (fun z => -h z) 0 (dotProductEquiv ℝ (Fin m) uStar) := by
      intro u
      have hineq := hu u
      let a : EReal := (((uStar ⬝ᵥ u : ℝ) : EReal))
      have h1 : a ≠ (⊥ : EReal) ∨ h 0 ≠ (⊥ : EReal) := Or.inl (by simp [a])
      have h2 : a ≠ (⊤ : EReal) ∨ h 0 ≠ (⊤ : EReal) := Or.inl (by simp [a])
      have hle_sub : h u ≤ h 0 - a :=
        (EReal.le_sub_iff_add_le (a := h u) (b := a) (c := h 0) h1 h2).2
          (by simpa [a, add_comm, add_left_comm, add_assoc] using hineq)
      have hraw : h u ≤ -(a + -h 0) := by
        have hneg_add : -(a + -h 0) = -a + h 0 := by
          have ha_bot : a ≠ (⊥ : EReal) := by simp [a]
          have ha_top : a ≠ (⊤ : EReal) := by simp [a]
          calc
            -(a + -h 0) = -a - (-h 0) :=
              EReal.neg_add (Or.inl ha_bot) (Or.inl ha_top)
            _ = -a + h 0 := by simp [sub_eq_add_neg]
        rw [hneg_add]
        simpa [a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hle_sub
      have hmon : a + -h 0 ≤ -h u := (EReal.le_neg).1 hraw
      simpa [a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmon
    simpa [concaveSubdifferentialAt, IsEuclideanSubgradientAt, subdifferentialAt] using hineq'

/-- Helper for Theorem 6.30.8: the perturbation supremum equals `h 0` exactly when the affine
terms are all bounded above by `h 0`; the value at `u = 0` supplies the reverse inequality. -/
lemma helperForTheorem_6_30_8_perturbationSup_eq_valueAt_zero_iff_pointwise_bound {m : ℕ}
    (h : (Fin m → ℝ) → EReal) (uStar : Fin m → ℝ) :
    (let S : EReal := sSup (Set.range fun u : Fin m → ℝ => (((uStar ⬝ᵥ u : ℝ) : EReal) + h u));
      S = h 0 ∧ S ≠ ⊤ ∧ S ≠ ⊥) ↔
      h 0 ≠ ⊤ ∧ h 0 ≠ ⊥ ∧
        ∀ u : Fin m → ℝ, (((uStar ⬝ᵥ u : ℝ) : EReal) + h u) ≤ h 0 := by
  let S : EReal := sSup (Set.range fun u : Fin m → ℝ => (((uStar ⬝ᵥ u : ℝ) : EReal) + h u))
  constructor
  · intro hS
    rcases hS with ⟨hEq, hTop, hBot⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [hEq] using hTop
    · simpa [hEq] using hBot
    · intro u
      -- Every affine term lies below the supremum, hence below `h 0` after rewriting.
      have hle : (((uStar ⬝ᵥ u : ℝ) : EReal) + h u) ≤ S := by
        exact le_sSup ⟨u, rfl⟩
      exact hEq.symm ▸ hle
  · rintro ⟨hTop, hBot, hBound⟩
    have hEq : S = h 0 := by
      -- The pointwise bound gives `S ≤ h 0`, and the `u = 0` term gives the reverse inequality.
      apply le_antisymm
      · refine sSup_le ?_
        rintro z ⟨u, rfl⟩
        exact hBound u
      · have hzero : (((uStar ⬝ᵥ (0 : Fin m → ℝ) : ℝ) : EReal) + h 0) ≤ S := by
          exact le_sSup ⟨0, rfl⟩
        simpa [S] using hzero
    refine ⟨hEq, ?_, ?_⟩
    · intro hSTop
      exact hTop (hEq ▸ hSTop)
    · intro hSBot
      exact hBot (hEq ▸ hSBot)

end Section30
end Chap06
