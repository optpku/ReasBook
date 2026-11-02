import Mathlib

open scoped Affine BigOperators

/-
Exercise 3.7 is an affine/linear-geometry item. The canonical owner declarations in this domain
are:

* `affineIndependent_iff_linearIndependent_vsub`;
* `linearIndependent_equiv` together with `finSuccAboveEquiv`;
* `linearIndependent_finSucc`.

The intrinsic bridge theorem is `affineIndependent_iff_linearIndependent_tail_vsub`, obtained by
reindexing `affineIndependent_iff_linearIndependent_vsub` along `Fin.succ`. The source-facing
homogeneous lift lives intrinsically in `V × k`; the coordinate `k^n` statements are special
cases.
-/

/-- The homogeneous lift `(x, 1)` of a vector `x`, viewed in `V × k`. -/
def homogeneousLift (k : Type*) [One k] {V : Type*} (x : V) : V × k :=
  (x, 1)

@[simp] theorem homogeneousLift_fst {k : Type*} [One k] {V : Type*} (x : V) :
    (homogeneousLift k x).1 = x :=
  rfl

@[simp] theorem homogeneousLift_snd {k : Type*} [One k] {V : Type*} (x : V) :
    (homogeneousLift k x).2 = 1 :=
  rfl

section Affine

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P]
variable (k)

/-- Reindexing `affineIndependent_iff_linearIndependent_vsub` along `Fin.succ` identifies affine
independence of a `Fin (q + 1)`-family with linear independence of the tail vectors based at the
zeroth point. -/
theorem affineIndependent_iff_linearIndependent_tail_vsub {q : ℕ} (p : Fin (q + 1) → P) :
    AffineIndependent k p ↔
      LinearIndependent k (fun i : Fin q ↦ p i.succ -ᵥ p 0) := by
  rw [affineIndependent_iff_linearIndependent_vsub k p 0]
  simpa [finSuccAboveEquiv_apply] using
    (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (q + 1))) :
      LinearIndependent k
          ((fun i : {j : Fin (q + 1) // j ≠ 0} ↦ (p i -ᵥ p 0 : V)) ∘
            finSuccAboveEquiv (0 : Fin (q + 1))) ↔
        LinearIndependent k
          (fun i : {j : Fin (q + 1) // j ≠ 0} ↦ (p i -ᵥ p 0 : V))).symm

variable {k}

end Affine

section RingModule

variable {k : Type*} {V : Type*}
variable [Ring k] [AddCommGroup V] [Module k V]

private lemma homogeneousLift_combination_eq_zero_iff {q : ℕ}
    (x : Fin (q + 1) → V) {s : Finset (Fin q)} {g : Fin q → k} :
    (-∑ i ∈ s, g i) • homogeneousLift k (x 0) +
        ∑ i ∈ s, g i • homogeneousLift k (x i.succ) = 0 ↔
      ∑ i ∈ s, g i • (x i.succ - x 0) = 0 := by
  constructor
  · intro h
    have hfst :
        (-∑ i ∈ s, g i) • x 0 + ∑ i ∈ s, g i • x i.succ = 0 := by
      simpa [homogeneousLift, Prod.fst_sum] using congrArg Prod.fst h
    calc
      ∑ i ∈ s, g i • (x i.succ - x 0)
          = ∑ i ∈ s, g i • x i.succ - (∑ i ∈ s, g i) • x 0 := by
              simp [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
      _ = 0 := by
            simpa [sub_eq_add_neg, add_comm, neg_smul] using hfst
  · intro h
    apply Prod.ext
    · calc
        ((-∑ i ∈ s, g i) • homogeneousLift k (x 0) +
            ∑ i ∈ s, g i • homogeneousLift k (x i.succ)).1
            = (-∑ i ∈ s, g i) • x 0 + ∑ i ∈ s, g i • x i.succ := by
                simp [homogeneousLift, Prod.fst_sum]
        (-∑ i ∈ s, g i) • x 0 + ∑ i ∈ s, g i • x i.succ
            = ∑ i ∈ s, g i • x i.succ - (∑ i ∈ s, g i) • x 0 := by
                simp [sub_eq_add_neg, add_comm, neg_smul]
        _ = ∑ i ∈ s, g i • (x i.succ - x 0) := by
              simp [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
        _ = 0 := h
    · simp [homogeneousLift, Prod.snd_sum]

/-- Exercise 3.7 (1). For points `x 0, x 1, ..., x q` in a `k`-module, affine independence is
equivalent to linear independence of the difference vectors `x 1 - x 0, ..., x q - x 0`. -/
theorem affineIndependent_iff_linearIndependent_tail_sub {q : ℕ}
    (x : Fin (q + 1) → V) :
    AffineIndependent k x ↔
      LinearIndependent k (fun i : Fin q ↦ x i.succ - x 0) := by
  simpa [vsub_eq_sub] using affineIndependent_iff_linearIndependent_tail_vsub k x

end RingModule

section DivisionRingModule

variable {k : Type*} {V : Type*}
variable [DivisionRing k] [AddCommGroup V] [Module k V]

/-- Exercise 3.7 (2). The difference vectors `x 1 - x 0, ..., x q - x 0` are linearly independent
if and only if the lifted vectors `(x 0, 1), ..., (x q, 1)` in `V × k` are linearly independent. -/
theorem linearIndependent_tail_sub_iff_linearIndependent_homogeneous_lift {q : ℕ}
    (x : Fin (q + 1) → V) :
    LinearIndependent k (fun i : Fin q ↦ x i.succ - x 0) ↔
      LinearIndependent k (homogeneousLift k ∘ x) := by
  constructor
  · intro hdiff
    rw [linearIndependent_finSucc]
    change
      LinearIndependent k (fun i : Fin q ↦ homogeneousLift k (x i.succ)) ∧
        homogeneousLift k (x 0) ∉
          Submodule.span k (Set.range (fun i : Fin q ↦ homogeneousLift k (x i.succ)))
    constructor
    · rw [linearIndependent_iff']
      intro s g hg i hi
      have hsum : ∑ j ∈ s, g j = 0 := by
        simpa [homogeneousLift, Prod.snd_sum] using congrArg Prod.snd hg
      have hvec : ∑ j ∈ s, g j • x j.succ = 0 := by
        simpa [homogeneousLift, Prod.fst_sum] using congrArg Prod.fst hg
      have hdiff' : ∑ j ∈ s, g j • (x j.succ - x 0) = 0 := by
        calc
          ∑ j ∈ s, g j • (x j.succ - x 0)
              = ∑ j ∈ s, g j • x j.succ - ∑ j ∈ s, g j • x 0 := by
                  simp [smul_sub, Finset.sum_sub_distrib]
          _ = ∑ j ∈ s, g j • x j.succ - (∑ j ∈ s, g j) • x 0 := by
                rw [Finset.sum_smul]
          _ = 0 := by simp [hsum, hvec]
      exact (linearIndependent_iff'.1 hdiff) s g hdiff' i hi
    · intro hx
      rcases (Submodule.mem_span_range_iff_exists_fun k).1 hx with ⟨c, hc⟩
      have hsum : ∑ i, c i = 1 := by
        simpa [homogeneousLift, Prod.snd_sum] using congrArg Prod.snd hc
      have hvec : ∑ i, c i • x i.succ = x 0 := by
        simpa [homogeneousLift, Prod.fst_sum] using congrArg Prod.fst hc
      have hcomb : ∑ i, c i • (x i.succ - x 0) = 0 := by
        calc
          ∑ i, c i • (x i.succ - x 0)
              = ∑ i, c i • x i.succ - ∑ i, c i • x 0 := by
                  simp [smul_sub, Finset.sum_sub_distrib]
          _ = ∑ i, c i • x i.succ - (∑ i, c i) • x 0 := by
                rw [Finset.sum_smul]
          _ = x 0 - 1 • x 0 := by simp [hvec, hsum]
          _ = 0 := by simp
      have hc_zero := (linearIndependent_iff'.1 hdiff) Finset.univ c hcomb
      have hsum_zero : ∑ i, c i = 0 := by
        simp [hc_zero]
      have h10 : (1 : k) = 0 := by rw [← hsum, hsum_zero]
      exact one_ne_zero h10
  · intro hlift
    rw [linearIndependent_iff']
    intro s g hg i hi
    let gLift : Fin (q + 1) → k := Fin.cases (-∑ j ∈ s, g j) g
    have hzero :
        ∑ j ∈ insert 0 (s.map (Fin.succEmb q)), gLift j • homogeneousLift k (x j) = 0 := by
      have hs0 : (0 : Fin (q + 1)) ∉ s.map (Fin.succEmb q) := by
        intro hs0
        rcases Finset.mem_map.1 hs0 with ⟨j, _, hj⟩
        simp at hj
      rw [Finset.sum_insert hs0, Finset.sum_map]
      simpa [gLift] using (homogeneousLift_combination_eq_zero_iff x).2 hg
    have hg_zero := (linearIndependent_iff'.1 hlift) (insert 0 (s.map (Fin.succEmb q))) gLift hzero
    simpa [gLift] using
      hg_zero i.succ (by exact Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, hi, rfl⟩))

/-- Exercise 3.7 (3). For points `x 0, x 1, ..., x q` in a `k`-module, affine independence is
equivalent to linear independence of the lifted vectors `(x 0, 1), ..., (x q, 1)` in `V × k`. -/
theorem affineIndependent_iff_linearIndependent_homogeneous_lift {q : ℕ}
    (x : Fin (q + 1) → V) :
    AffineIndependent k x ↔
      LinearIndependent k (homogeneousLift k ∘ x) :=
  (affineIndependent_iff_linearIndependent_tail_sub x).trans
    (linearIndependent_tail_sub_iff_linearIndependent_homogeneous_lift x)

end DivisionRingModule
