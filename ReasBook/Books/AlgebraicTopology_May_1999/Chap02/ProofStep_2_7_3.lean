/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open unitInterval

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- Helper for ProofStep 2.7.3: if we stop the canonical `addNSMul` partition of the unit interval
at the first index where it reaches `1`, then the remaining prefix is strictly increasing. -/
lemma first_terminal_addNSMul_strictMono {δ : ℝ} (hδ : 0 < δ) :
    StrictMono
      (fun k : Fin (Nat.ceil (1 / δ) + 1) ↦
        Set.Icc.addNSMul zero_le_one δ k) := by
  let N : ℕ := Nat.ceil (1 / δ)
  let g : Fin (N + 1) → I := fun k ↦ Set.Icc.addNSMul zero_le_one δ k.1
  have hmono : Monotone (fun n : ℕ ↦ Set.Icc.addNSMul zero_le_one δ n) :=
    Set.Icc.monotone_addNSMul zero_le_one hδ.le
  have hg : StrictMono g := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    change Set.Icc.addNSMul zero_le_one δ k.1 < Set.Icc.addNSMul zero_le_one δ k.succ.1
    have hk_lt_div : (k.1 : ℝ) < 1 / δ := by
      -- Indices below `⌈1 / δ⌉₊` lie strictly before the terminal time.
      exact (Nat.lt_ceil).1 (by simpa [N] using k.is_lt)
    have hk_lt_one : ((k.1 : ℕ) • δ : ℝ) < 1 := by
      -- On this prefix, repeated addition by `δ` has not yet reached `1`.
      simpa [nsmul_eq_mul] using (lt_div_iff₀ hδ).mp hk_lt_div
    have hle :
        Set.Icc.addNSMul zero_le_one δ k.1 ≤ Set.Icc.addNSMul zero_le_one δ k.succ.1 := by
      simpa using hmono (Nat.le_succ k.1)
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hk_lt_one : (k.1 : ℕ) • δ < (1 : ℝ) := by
      simpa [nsmul_eq_mul] using (lt_div_iff₀ hδ).mp hk_lt_div
    have hk_succ_lt_one : (k.succ.1 : ℕ) • δ < (1 : ℝ) := by
      -- If two consecutive points were equal, the later one would also lie below `1`.
      have hEq_coe_subtype :
          (Set.Icc.addNSMul zero_le_one δ k.1 : ℝ) =
            (Set.Icc.addNSMul zero_le_one δ k.succ.1 : ℝ) :=
        congrArg (fun z : I ↦ (z : ℝ)) hEq
      have hk_mem : ((k.1 : ℕ) • δ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · positivity
        · exact hk_lt_one.le
      have hk_val :
          Set.Icc.addNSMul zero_le_one δ k.1 = ⟨(k.1 : ℕ) • δ, hk_mem⟩ := by
        simpa [Set.Icc.addNSMul, zero_add] using
          (Set.projIcc_of_mem (h := zero_le_one) hk_mem)
      have hk_succ_ne_one : Set.Icc.addNSMul zero_le_one δ k.succ.1 ≠ 1 := by
        intro hk_succ_eq
        have hk_eq_one : Set.Icc.addNSMul zero_le_one δ k.1 = 1 := hEq.trans hk_succ_eq
        have hk_eq_one_coe : ((k.1 : ℕ) • δ : ℝ) = 1 := by
          rw [hk_val] at hk_eq_one
          exact congrArg (fun z : I ↦ (z : ℝ)) hk_eq_one
        linarith
      refine lt_of_not_ge ?_
      intro hk_ge_one
      exact hk_succ_ne_one (by
        simpa [Set.Icc.addNSMul, zero_add] using
          (projIcc_eq_one (x := (k.succ.1 : ℕ) • δ)).2 hk_ge_one)
    have hk_mem : ((k.1 : ℕ) • δ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact hk_lt_one.le
    have hk_succ_mem : ((k.succ.1 : ℕ) • δ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact hk_succ_lt_one.le
    have hk_val :
        Set.Icc.addNSMul zero_le_one δ k.1 = ⟨(k.1 : ℕ) • δ, hk_mem⟩ := by
      -- On the unsaturated prefix, `addNSMul` is just repeated addition by `δ`.
      simpa [Set.Icc.addNSMul, zero_add] using
        (Set.projIcc_of_mem (h := zero_le_one) hk_mem)
    have hk_succ_val :
        Set.Icc.addNSMul zero_le_one δ k.succ.1 = ⟨(k.succ.1 : ℕ) • δ, hk_succ_mem⟩ := by
      simpa [Set.Icc.addNSMul, zero_add] using
        (Set.projIcc_of_mem (h := zero_le_one) hk_succ_mem)
    have hEq_coe_raw :
        (Set.Icc.addNSMul zero_le_one δ k.1 : ℝ) =
          (Set.Icc.addNSMul zero_le_one δ k.succ.1 : ℝ) :=
      congrArg (fun z : I ↦ (z : ℝ)) hEq
    have hEq_coe : ((k.1 : ℕ) • δ : ℝ) = ((k.succ.1 : ℕ) • δ : ℝ) := by
      rw [hk_val, hk_succ_val] at hEq_coe_raw
      simpa using hEq_coe_raw
    have hEq_add : ((k.1 : ℕ) • δ : ℝ) = ((k.1 : ℕ) • δ : ℝ) + δ := by
      calc
        ((k.1 : ℕ) • δ : ℝ) = ((k.succ.1 : ℕ) • δ : ℝ) := hEq_coe
        _ = ((k.1 : ℕ) • δ : ℝ) + δ := by
          simpa using (succ_nsmul (a := δ) (n := k.1))
    linarith
  simpa [N, g]

/-- Helper for ProofStep 2.7.3: the image of a truncated path is controlled by the original path on
the corresponding closed subinterval. -/
lemma truncate_range_subset_image_Icc {x y : X} (γ : Path x y) {a b : I} (hab : a ≤ b) :
    Set.range (γ.truncate a b) ⊆ γ '' Set.Icc a b := by
  intro z hz
  rcases hz with ⟨s, rfl⟩
  let u : ℝ := min (max (s : ℝ) a) b
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨by
      dsimp [u]
      exact le_min (le_trans a.2.1 (le_max_right _ _)) b.2.1, by
      dsimp [u]
      exact le_trans (min_le_left _ _) (max_le s.2.2 a.2.2)⟩
  let uI : I := ⟨u, hu⟩
  have hu_ab : uI ∈ Set.Icc a b := by
    exact ⟨by
      change (a : ℝ) ≤ u
      dsimp [u]
      exact le_min (le_max_right _ _) hab, by
      change u ≤ (b : ℝ)
      dsimp [u]
      exact min_le_right _ _⟩
  refine ⟨uI, hu_ab, ?_⟩
  -- The truncation parameter already lies in `I`, so `extend` agrees with the original path.
  simpa [Path.truncate, u, uI] using (γ.extend_extends' uI).symm

/-- Helper for ProofStep 2.7.3: if one closed interval lies in the pullback of a cover member, then
the corresponding truncated path stays inside that cover member. -/
lemma truncate_subordinate_of_interval_subset
    {x y : X} (γ : Path x y) {O : ι → TopologicalSpace.Opens X} {i : ι} {a b : I}
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ (fun s : I ↦ γ s) ⁻¹' (O i : Set X)) :
    Set.range (γ.truncate a b) ⊆ O i := by
  intro z hz
  rcases truncate_range_subset_image_Icc (γ := γ) hab hz with ⟨s, hs, rfl⟩
  exact hsub hs

/-- ProofStep 2.7.3: every path in `X` admits a finite subdivision whose successive subpaths lie
in members of an open cover `O`; this is the geometric input showing that compatible data on the
fundamental groupoids `Π(U)` determine a value on each path class in `Π(X)`. -/
-- Proof sketch: pull back the cover `O` along `γ : I → X`, apply the canonical mathlib partition
-- lemma `exists_monotone_Icc_subset_open_cover_unitInterval`, and then discard repetitions at the
-- terminal value `1` to obtain strictly increasing break points. The subinterval-covering
-- conclusion for the pulled-back cover translates to the desired containment of each truncated
-- subpath by `Path.truncate_range`.
theorem path_subdivision_subordinate_to_open_cover
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    ∃ n : ℕ, ∃ t : Fin (n + 1) → I,
      t 0 = 0 ∧
      t (Fin.last n) = 1 ∧
      StrictMono t ∧
      ∃ i : Fin n → ι,
        ∀ k : Fin n, Set.range (γ.truncate (t k.castSucc) (t k.succ)) ⊆ O (i k) := by
  classical
  let c : ι → Set I := fun i ↦ (fun s : I ↦ γ s) ⁻¹' (O i : Set X)
  have hc₁ : ∀ i, IsOpen (c i) := by
    -- Pull the cover back along the path to obtain an open cover of the unit interval.
    intro i
    exact (O i).isOpen.preimage γ.continuous
  have hc₂ : Set.univ ⊆ ⋃ i, c i := by
    -- Every point of the path lies in some member of the ambient open cover.
    intro s _
    obtain ⟨i, hi⟩ := hO.exists_mem (γ s)
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨δ, δ_pos, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ : 0 < δ / 2 := half_pos δ_pos
  let tNat : ℕ → I := Set.Icc.addNSMul zero_le_one (δ / 2)
  let n : ℕ := Nat.ceil (1 / (δ / 2))
  have hmono : Monotone tNat := by
    exact Set.Icc.monotone_addNSMul zero_le_one hδ.le
  have hsub :
      ∀ m, ∃ i, Set.Icc (tNat m) (tNat (m + 1)) ⊆ c i := by
    intro m
    obtain ⟨i, hi⟩ := hball (tNat m) trivial
    refine ⟨i, ?_⟩
    intro s hs
    exact hi ((Set.Icc.abs_sub_addNSMul_le zero_le_one hδ.le m hs).trans_lt (half_lt_self δ_pos))
  let t : Fin (n + 1) → I := fun k ↦ tNat k.1
  have ht0 : t 0 = 0 := by
    -- The canonical partition starts at the left endpoint of the interval.
    simpa [t, tNat] using (Set.Icc.addNSMul_zero (h := zero_le_one) (δ := δ / 2))
  have ht1 : t (Fin.last n) = 1 := by
    -- The ceiling choice of `n` forces the final breakpoint to reach the terminal value `1`.
    apply Subtype.ext
    have hn_div : (1 / (δ / 2) : ℝ) ≤ n := by
      simpa [n] using (Nat.le_ceil (1 / (δ / 2) : ℝ))
    have hn_reaches_one : (1 : ℝ) ≤ (n : ℕ) • (δ / 2) := by
      simpa [nsmul_eq_mul] using (div_le_iff₀ hδ).mp hn_div
    simpa [t, tNat, n, Set.Icc.addNSMul, zero_add] using
      (projIcc_eq_one (x := (n : ℕ) • (δ / 2))).2 hn_reaches_one
  have hstrict : StrictMono t := by
    -- Route correction: keep the concrete `addNSMul` witness so strictness is proved by trimming
    -- only the terminal repetitions, rather than by postprocessing an abstract monotone partition.
    simpa [t, tNat, n] using first_terminal_addNSMul_strictMono (δ := δ / 2) hδ
  have hpieces :
      ∀ k : Fin n, ∃ i, Set.range (γ.truncate (t k.castSucc) (t k.succ)) ⊆ O i := by
    intro k
    obtain ⟨i, hi⟩ := hsub k.1
    have hle : t k.castSucc ≤ t k.succ := by
      simpa [t, tNat] using hmono (Nat.le_succ k.1)
    -- The pullback-cover control on the interval translates directly to the truncated subpath.
    refine ⟨i, truncate_subordinate_of_interval_subset (γ := γ) hle ?_⟩
    simpa [t, tNat, c] using hi
  choose i hi using hpieces
  refine ⟨n, t, ht0, ht1, hstrict, i, ?_⟩
  -- The chosen cover labels witness the subordinate-cover property interval by interval.
  intro k
  exact hi k
